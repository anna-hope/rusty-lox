use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::ops::{Div, Mul, Sub};
use std::rc::Rc;
use std::time::SystemTime;
use std::{env, fmt};

use fnv::FnvHashMap;
use thiserror::Error;
use ustr::Ustr;

use crate::value::{Function, NativeFn, ObjNative};
use crate::{
    chunk::OpCode,
    compiler::{Parser, ParserError},
    value::{BoxedValue, Value},
};

const FRAMES_MAX: usize = 64;
const STACK_MAX: usize = FRAMES_MAX * 256;

pub type Result<T> = std::result::Result<T, InterpretError>;

type Stack = Vec<BoxedValue>;

#[derive(Debug, Error)]
pub enum InterpretError {
    #[error("Compile error")]
    Compile(#[from] ParserError),

    #[error("Runtime error: {0}")]
    Runtime(String),
}

#[derive(Debug)]
struct CallFrame {
    function: Rc<Function>,
    ip: usize,
    stack_offset: usize,
}

impl CallFrame {
    fn new(function: Rc<Function>, stack_offset: usize) -> Self {
        Self {
            function,
            ip: 0,
            stack_offset,
        }
    }
}

#[derive(Debug, Default)]
pub struct Vm {
    frames: Vec<Rc<RefCell<CallFrame>>>,
    stack: Stack,
    globals: FnvHashMap<Ustr, BoxedValue>,
}

impl Vm {
    pub fn new() -> Self {
        // Set aside the first stack slot for methods later.
        let mut stack = Vec::with_capacity(STACK_MAX);
        stack.push(Rc::new(Value::Nil));

        let mut vm = Self {
            frames: Vec::with_capacity(FRAMES_MAX),
            stack,
            globals: FnvHashMap::default(),
        };
        vm.define_native("clock", clock_native);
        vm
    }

    pub fn interpret(&mut self, source: String) -> Result<()> {
        let mut parser = Parser::new(source);
        let function = Rc::new(parser.compile()?);
        self.stack
            .push(Rc::new(Value::Function(Rc::clone(&function))));

        self.call(function, 0).unwrap();
        self.run()
    }

    fn run(&mut self) -> Result<()> {
        let mut frame = Rc::clone(self.frames.last().unwrap());
        let mut chunk = Rc::clone(&frame.borrow().function.chunk);

        let trace_execution = env::var("DEBUG_TRACE_EXECUTION") == Ok("1".into());

        loop {
            let code = chunk.borrow().codes[frame.borrow().ip];

            if trace_execution {
                println!("          ");
                for slot in self.stack.iter() {
                    println!("[ {slot:?} ]");
                }
                chunk.borrow().disassemble_instruction(frame.borrow().ip);
            }

            frame.borrow_mut().ip += 1;

            match code {
                OpCode::Print => {
                    println!("{}", self.stack.pop().unwrap());
                }
                OpCode::Jump(offset) => {
                    frame.borrow_mut().ip += offset;
                }
                OpCode::JumpIfFalse(offset) => {
                    if self.stack.last().unwrap().is_falsey() {
                        frame.borrow_mut().ip += offset;
                    }
                }
                OpCode::Loop(offset) => {
                    frame.borrow_mut().ip -= offset;
                }
                OpCode::Call(arg_count) => {
                    let callee = {
                        // Go past the function arguments to get the function Value from the stack.
                        self.stack
                            .get(self.stack.len() - arg_count - 1)
                            .unwrap()
                            .clone()
                    };
                    self.call_value(callee, arg_count)?;
                    frame = Rc::clone(self.frames.last().unwrap());
                    chunk = frame.borrow().function.chunk.clone();
                }
                OpCode::Return => {
                    let result = self.stack.pop().unwrap();
                    self.frames.pop();
                    if self.frames.is_empty() {
                        self.stack.pop();
                        return Ok(());
                    }
                    self.stack.truncate(frame.borrow().stack_offset);
                    self.stack.push(result);
                    frame = Rc::clone(self.frames.last().unwrap());
                    chunk = frame.borrow().function.chunk.clone();
                }
                OpCode::Constant(index) => {
                    let constant = chunk.borrow().read_constant(index).clone();
                    self.stack.push(Rc::new(constant));
                }
                OpCode::Nil => self.stack.push(Rc::new(Value::Nil)),
                OpCode::True => self.stack.push(Rc::new(true.into())),
                OpCode::False => self.stack.push(Rc::new(false.into())),
                OpCode::Pop => {
                    self.stack.pop();
                }
                OpCode::GetLocal(slot) => {
                    let slot = slot + frame.borrow().stack_offset;
                    let maybe_value = self.stack.get(slot).cloned();
                    if let Some(value) = maybe_value {
                        self.stack.push(value);
                    } else {
                        return Err(
                            self.runtime_error(format!("Could not access stack slot {slot}"))
                        );
                    }
                }
                OpCode::SetLocal(slot) => {
                    let slot = slot + frame.borrow().stack_offset;
                    // Have to add 1 to the slot with offset here because
                    // reasons.
                    let value = self.stack.get(slot + 1).unwrap().clone();
                    self.stack[slot] = value;
                }
                OpCode::GetGlobal(slot) => {
                    let name = chunk.borrow().read_constant(slot).name().unwrap();
                    if let Some(variable) = self.globals.get(&name) {
                        self.stack.push(variable.clone());
                    } else {
                        return Err(self.runtime_error(format!("Undefined variable: {name}")));
                    }
                }
                OpCode::DefineGlobal(slot) => {
                    let name = chunk.borrow().read_constant(slot).name().unwrap();
                    self.globals
                        .insert(name, self.stack.last().unwrap().clone());
                    self.stack.pop();
                }
                OpCode::SetGlobal(slot) => {
                    let name = chunk.borrow().read_constant(slot).name().unwrap();
                    if let Entry::Occupied(mut e) = self.globals.entry(name) {
                        e.insert(self.stack.last().unwrap().clone());
                    } else {
                        return Err(self.runtime_error(format!("Undefined variable '{name}'")));
                    }
                }
                OpCode::Equal => {
                    let b = self.stack.pop().unwrap();
                    let a = self.stack.pop().unwrap();
                    self.stack.push(Rc::new((a == b).into()));
                }
                OpCode::Greater => comparison_op(&mut self.stack, PartialOrd::gt)?,
                OpCode::Less => comparison_op(&mut self.stack, PartialOrd::lt)?,
                OpCode::Add => {
                    let a = self.stack.get(self.stack.len() - 2).unwrap().clone();
                    let b = self.stack.last().unwrap().clone();

                    match (a.as_ref(), b.as_ref()) {
                        (Value::String(a), Value::String(b)) => {
                            self.stack.pop();
                            self.stack.pop();
                            let a = a.replace('"', "");
                            let b = b.replace('"', "");
                            let result = format!("\"{}\"", a + b.as_str());
                            self.stack.push(Rc::new(result.into()));
                        }
                        (Value::Number(a), Value::Number(b)) => {
                            self.stack.pop();
                            self.stack.pop();
                            self.stack.push(Rc::new((a + b).into()));
                        }
                        _ => {
                            return Err(self.runtime_error(format!(
                                "Operands must be two numbers or two strings, got {a} and {b}."
                            )));
                        }
                    }
                }
                OpCode::Subtract => binary_op(&mut self.stack, Sub::sub)?,
                OpCode::Multiply => binary_op(&mut self.stack, Mul::mul)?,
                OpCode::Divide => binary_op(&mut self.stack, Div::div)?,
                OpCode::Not => {
                    let bool_val = self.stack.pop().unwrap().is_falsey();
                    self.stack.push(Rc::new(bool_val.into()));
                }
                OpCode::Negate => {
                    // Inspect the value from the stack without popping it first,
                    // in case it's not a number.
                    let value = self.stack.last().unwrap().clone();

                    match value.as_ref() {
                        Value::Number(value) => {
                            self.stack.pop();
                            self.stack.push(Rc::new(Value::Number(-*value)))
                        }
                        _ => {
                            return Err(self.runtime_error("Operand must be a number."));
                        }
                    }
                }
            }
        }
    }

    fn call(&mut self, function: Rc<Function>, arg_count: usize) -> Result<()> {
        if arg_count > function.arity {
            return Err(self.runtime_error(format!(
                "Expected {} arguments but got {arg_count}.",
                function.arity
            )));
        }

        if self.frames.len() == FRAMES_MAX {
            return Err(self.runtime_error("Stack overflow."));
        }

        let stack_offset = self.stack.len() - arg_count - 1;
        let frame = Rc::new(RefCell::new(CallFrame::new(function, stack_offset)));
        self.frames.push(frame);
        Ok(())
    }

    fn call_value(&mut self, callee: Rc<Value>, arg_count: usize) -> Result<()> {
        match callee.as_ref() {
            Value::Function(function) => self.call(Rc::clone(function), arg_count),
            Value::ObjNative(native) => {
                let stack_len = self.stack.len();
                let args = &mut self.stack.as_mut_slice()[0..stack_len - arg_count];
                let result = (native.function)(arg_count, args);
                for _ in 0..arg_count + 1 {
                    self.stack.pop();
                }
                self.stack.push(Rc::new(result));
                Ok(())
            }
            _ => Err(self.runtime_error("Can only call functions and classes.")),
        }
    }

    fn runtime_error(&self, msg: impl fmt::Display) -> InterpretError {
        let mut full_msg = format!("{msg}\n");
        for frame in self.frames.iter() {
            let frame = frame.borrow();
            let function = &frame.function;
            // -1 because the ip has already moved on to the next instruction
            // but we want the stack trace to point to the previous failed instruction.
            let line = function.chunk.borrow().lines[frame.ip - 1];

            full_msg.push_str(format!("line {line} in ").as_str());
            if let Some(name) = function.name {
                full_msg.push_str(format!("{name}\n").as_str());
            } else {
                full_msg.push_str("script\n");
            }
        }
        InterpretError::Runtime(full_msg)
    }

    fn define_native(&mut self, name: &str, function: NativeFn) {
        let native_fn_val = Rc::new(Value::ObjNative(ObjNative::new(function)));

        // Push onto the stack to prevent them from being collected by GC.
        self.stack.push(Rc::new(Value::String(name.into())));
        self.stack.push(Rc::clone(&native_fn_val));
        self.globals.insert(name.into(), native_fn_val);

        self.stack.pop();
        self.stack.pop();
    }
}

fn binary_op<F>(stack: &mut Stack, op: F) -> Result<()>
where
    F: Fn(f64, f64) -> f64,
{
    let b = stack.last().unwrap().clone();
    let a = stack.get(stack.len() - 2).unwrap().clone();

    match (a.as_ref(), b.as_ref()) {
        (Value::Number(a), Value::Number(b)) => {
            stack.pop();
            stack.pop();
            let result = op(*a, *b);
            stack.push(Rc::new(result.into()));
        }
        _ => {
            // runtime_error();
            return Err(InterpretError::Runtime(
                "Operands must be numbers.".to_string(),
            ));
        }
    }
    Ok(())
}

fn comparison_op<F>(stack: &mut Stack, op: F) -> Result<()>
where
    F: Fn(&f64, &f64) -> bool,
{
    let b = stack.last().unwrap().clone();
    let a = stack.get(stack.len() - 2).unwrap().clone();

    match (a.as_ref(), b.as_ref()) {
        (Value::Number(a), Value::Number(b)) => {
            stack.pop();
            stack.pop();
            let result = op(a, b);
            stack.push(Rc::new(result.into()));
        }
        _ => {
            return Err(InterpretError::Runtime(
                "Operands must be numbers.".to_string(),
            ));
        }
    }
    Ok(())
}

fn clock_native(_arg_count: usize, _args: &mut [BoxedValue]) -> Value {
    SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap()
        .as_secs_f64()
        .into()
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//
//     #[test]
//     fn evaluate_bool() {
//         let input = "!(5 - 4 > 3 * 2 == !nil);";
//         let mut vm = Vm::new();
//         let value = &vm.interpret(input.to_string()).unwrap()[0];
//         assert_eq!(value, &Value::Bool(true));
//     }
//
//     #[test]
//     fn evaluate_string() {
//         let input = r#"
// var beverage = "cafe au lait";
// var breakfast = "beignets with " + beverage;
// breakfast;
// "#;
//         let mut vm = Vm::new();
//         let result = &vm.interpret(input.to_string()).unwrap();
//         dbg!(&result);
//         dbg!(&vm.stack);
//         // assert_eq!(value, &Value::String("beignets with cafe au lait".into()));
//     }
// }
