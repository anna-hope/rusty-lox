use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::ops::{Div, Mul, Sub};
use std::rc::Rc;
use std::{env, fmt};

use fnv::FnvHashMap;
use thiserror::Error;
use ustr::Ustr;

use crate::value::Function;
use crate::{
    chunk::OpCode,
    compiler::{Parser, ParserError},
    value::Value,
};

const FRAMES_MAX: usize = 64;
const STACK_MAX: usize = FRAMES_MAX * 256;

pub type Result<T> = std::result::Result<T, InterpretError>;

type Stack = Vec<Value>;
type BoxedStack = Rc<RefCell<Stack>>;

#[derive(Debug, Error)]
pub enum InterpretError {
    #[error("Compile error")]
    Compile(#[from] ParserError),

    #[error("Runtime error: {0}")]
    Runtime(String),
}

#[derive(Debug)]
struct CallFrame {
    function: Function,
    ip: usize,
    slots: BoxedStack,
    stack_offset: usize,
}

impl CallFrame {
    fn new(function: Function, slots: BoxedStack, stack_offset: usize) -> Self {
        Self {
            function,
            ip: 0,
            slots,
            stack_offset,
        }
    }
}

#[derive(Debug, Default)]
pub struct Vm {
    frames: Vec<Rc<RefCell<CallFrame>>>,
    stack: BoxedStack,
    globals: FnvHashMap<Ustr, Value>,
}

impl Vm {
    pub fn new() -> Self {
        // Set aside the first stack slot for methods later.
        let mut stack = Vec::with_capacity(STACK_MAX);
        stack.push(Value::Nil);

        Self {
            frames: Vec::with_capacity(FRAMES_MAX),
            stack: Rc::new(RefCell::new(stack)),
            globals: FnvHashMap::default(),
        }
    }

    pub fn interpret(&mut self, source: String) -> Result<()> {
        let mut parser = Parser::new(source);
        let function = parser.compile()?;
        self.stack.borrow_mut().push(function.clone().into());

        self.call(function, 0).unwrap();
        self.run()
    }

    fn run(&mut self) -> Result<()> {
        let mut frame = Rc::clone(self.frames.last().unwrap());
        let mut chunk = frame.borrow().function.chunk.clone();

        loop {
            let code = chunk.codes[frame.borrow().ip];

            if env::var("DEBUG_TRACE_EXECUTION") == Ok("1".into()) {
                println!("          ");
                for slot in self.stack.borrow().iter() {
                    println!("[ {slot:?} ]");
                }
                chunk.disassemble_instruction(frame.borrow().ip);
            }

            frame.borrow_mut().ip += 1;

            match code {
                OpCode::Print => {
                    println!("{}", self.stack.borrow_mut().pop().unwrap());
                }
                OpCode::Jump(offset) => {
                    frame.borrow_mut().ip += offset;
                }
                OpCode::JumpIfFalse(offset) => {
                    if self.stack.borrow().last().unwrap().is_falsey() {
                        frame.borrow_mut().ip += offset;
                    }
                }
                OpCode::Loop(offset) => {
                    frame.borrow_mut().ip -= offset;
                }
                OpCode::Call(arg_count) => {
                    let callee = {
                        let stack = self.stack.borrow();
                        // Go past the function arguments to get the function Value from the stack.
                        stack.get(stack.len() - arg_count - 1).unwrap().clone()
                    };
                    self.call_value(callee, arg_count)?;
                    frame = Rc::clone(self.frames.last().unwrap());
                    chunk = frame.borrow().function.chunk.clone();
                }
                OpCode::Return => {
                    let mut stack = self.stack.borrow_mut();
                    let result = stack.pop().unwrap();
                    self.frames.pop();
                    if self.frames.is_empty() {
                        stack.pop();
                        return Ok(());
                    }
                    stack.push(result);
                    frame = Rc::clone(self.frames.last().unwrap());
                    chunk = frame.borrow().function.chunk.clone();
                }
                OpCode::Constant(index) => {
                    let constant = chunk.read_constant(index);
                    self.stack.borrow_mut().push(constant.clone());
                }
                OpCode::Nil => self.stack.borrow_mut().push(Value::Nil),
                OpCode::True => self.stack.borrow_mut().push(true.into()),
                OpCode::False => self.stack.borrow_mut().push(false.into()),
                OpCode::Pop => {
                    self.stack.borrow_mut().pop();
                }
                OpCode::GetLocal(slot) => {
                    let slot = slot + frame.borrow().stack_offset;
                    let value = frame.borrow().slots.borrow().get(slot).unwrap().clone();
                    self.stack.borrow_mut().push(value);
                }
                OpCode::SetLocal(slot) => {
                    let slot = slot + frame.borrow().stack_offset;
                    // Have to add 1 to the slot with offset here because
                    // reasons.
                    let value = frame.borrow().slots.borrow().get(slot + 1).unwrap().clone();
                    self.stack.borrow_mut()[slot] = value;
                }
                OpCode::GetGlobal(slot) => {
                    let value = chunk.read_constant(slot);
                    let name = value.name().unwrap();
                    if let Some(variable) = self.globals.get(&name) {
                        self.stack.borrow_mut().push(variable.clone());
                    } else {
                        return Err(self.runtime_error(format!("Undefined variable: {name}")));
                    }
                }
                OpCode::DefineGlobal(slot) => {
                    let value = chunk.read_constant(slot);
                    let name = value.name().unwrap();
                    self.globals
                        .insert(name, self.stack.borrow().last().unwrap().clone());
                    self.stack.borrow_mut().pop();
                }
                OpCode::SetGlobal(slot) => {
                    let value = chunk.read_constant(slot);
                    let name = value.name().unwrap();
                    if let Entry::Occupied(mut e) = self.globals.entry(name) {
                        e.insert(self.stack.borrow().last().unwrap().clone());
                    } else {
                        return Err(self.runtime_error(format!("Undefined variable '{name}'")));
                    }
                }
                OpCode::Equal => {
                    let mut stack = self.stack.borrow_mut();
                    let b = stack.pop().unwrap();
                    let a = stack.pop().unwrap();
                    self.stack.borrow_mut().push((a == b).into());
                }
                OpCode::Greater => comparison_op(&mut self.stack.borrow_mut(), PartialOrd::gt)?,
                OpCode::Less => comparison_op(&mut self.stack.borrow_mut(), PartialOrd::lt)?,
                OpCode::Add => {
                    let mut stack = self.stack.borrow_mut();
                    let a = stack.get(stack.len() - 2).unwrap().clone();
                    let b = stack.last().unwrap().clone();

                    match (a, b) {
                        (Value::String(a), Value::String(b)) => {
                            stack.pop();
                            stack.pop();
                            let a = a.replace('"', "");
                            let b = b.replace('"', "");
                            let result = format!("\"{}\"", a + b.as_str());
                            stack.push(result.into());
                        }
                        (Value::Number(a), Value::Number(b)) => {
                            stack.pop();
                            stack.pop();
                            stack.push((a + b).into());
                        }
                        _ => {
                            return Err(
                                self.runtime_error("Operands must be two numbers or two strings.")
                            );
                        }
                    }
                }
                OpCode::Subtract => binary_op(&mut self.stack.borrow_mut(), Sub::sub)?,
                OpCode::Multiply => binary_op(&mut self.stack.borrow_mut(), Mul::mul)?,
                OpCode::Divide => binary_op(&mut self.stack.borrow_mut(), Div::div)?,
                OpCode::Not => {
                    let mut stack = self.stack.borrow_mut();
                    let bool_val = stack.pop().unwrap().is_falsey();
                    stack.push(bool_val.into());
                }
                OpCode::Negate => {
                    // Inspect the value from the stack without popping it first,
                    // in case it's not a number.
                    let mut stack = self.stack.borrow_mut();
                    let value = stack.last().unwrap().clone();

                    match value {
                        Value::Number(value) => {
                            stack.pop();
                            stack.push(Value::Number(-value))
                        }
                        _ => {
                            return Err(self.runtime_error("Operand must be a number."));
                        }
                    }
                }
            }
        }
    }

    fn call(&mut self, function: Function, arg_count: usize) -> Result<()> {
        if arg_count > function.arity {
            return Err(self.runtime_error(format!(
                "Expected {} arguments but got {arg_count}.",
                function.arity
            )));
        }

        if self.frames.len() == FRAMES_MAX {
            return Err(self.runtime_error("Stack overflow."));
        }

        let stack_pointer = self.stack.borrow().len() - arg_count - 1;
        let frame = Rc::new(RefCell::new(CallFrame::new(
            function,
            Rc::clone(&self.stack),
            stack_pointer,
        )));
        self.frames.push(frame);
        Ok(())
    }

    fn call_value(&mut self, callee: Value, arg_count: usize) -> Result<()> {
        match callee {
            Value::Function(function) => self.call(function, arg_count),
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
            let line = function.chunk.lines[frame.ip - 1];

            full_msg.push_str(format!("line {line} in ").as_str());
            if let Some(name) = function.name {
                full_msg.push_str(format!("{name}\n").as_str());
            } else {
                full_msg.push_str("script\n");
            }
        }
        InterpretError::Runtime(full_msg)
    }
}

fn binary_op<F>(stack: &mut Vec<Value>, op: F) -> Result<()>
where
    F: Fn(f64, f64) -> f64,
{
    let b = stack.last().unwrap().clone();
    let a = stack.get(stack.len() - 2).unwrap().clone();

    match (a, b) {
        (Value::Number(a), Value::Number(b)) => {
            stack.pop();
            stack.pop();
            let result = op(a, b);
            stack.push(result.into());
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

fn comparison_op<F>(stack: &mut Vec<Value>, op: F) -> Result<()>
where
    F: Fn(&f64, &f64) -> bool,
{
    let b = stack.last().unwrap().clone();
    let a = stack.get(stack.len() - 2).unwrap().clone();

    match (a, b) {
        (Value::Number(a), Value::Number(b)) => {
            stack.pop();
            stack.pop();
            let result = op(&a, &b);
            stack.push(result.into());
        }
        _ => {
            return Err(InterpretError::Runtime(
                "Operands must be numbers.".to_string(),
            ));
        }
    }
    Ok(())
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
