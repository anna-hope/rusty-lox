use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::ops::{Div, Mul, Sub};
use std::rc::Rc;
use std::time::SystemTime;
use std::{env, fmt};

use fnv::FnvHashMap;
use thiserror::Error;
use ustr::Ustr;

use crate::value::ObjClass;
use crate::{
    chunk::OpCode,
    compiler::{Parser, ParserError},
    value::{
        BoxedObjClosure, BoxedObjUpvalue, BoxedValue, NativeFn, NativeFnResult, ObjClosure,
        ObjNative, ObjUpvalue, Value,
    },
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
    closure: BoxedObjClosure,
    ip: usize,
    stack_offset: usize,
}

impl CallFrame {
    fn new(closure: BoxedObjClosure, stack_offset: usize) -> Self {
        Self {
            closure,
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
    head_open_upvalue: Option<BoxedObjUpvalue>,
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
            head_open_upvalue: None,
        };

        vm.define_native("clock", clock_native);
        vm.define_native("refcount", refcount_native);
        vm
    }

    pub fn interpret(&mut self, source: String) -> Result<()> {
        let mut parser = Parser::new(source);
        let function = parser.compile()?;
        let closure = Rc::new(RefCell::new(ObjClosure::new(function)));
        self.stack
            .push(Rc::new(Value::Closure(Rc::clone(&closure))));

        self.call(closure, 0).unwrap();
        self.run()
    }

    fn run(&mut self) -> Result<()> {
        let mut frame = Rc::clone(self.frames.last().unwrap());
        let mut chunk = Rc::clone(&frame.borrow().closure.borrow().function.chunk);

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
                    // Go past the function arguments to get the function Value from the stack.
                    let callee = Rc::clone(&self.stack[self.stack.len() - arg_count - 1]);
                    self.call_value(callee, arg_count)?;
                    frame = Rc::clone(self.frames.last().unwrap());
                    chunk = Rc::clone(&frame.borrow().closure.borrow().function.chunk);
                }
                OpCode::Closure(index, upvalue_count) => {
                    let value = Rc::new(chunk.borrow().read_constant(index).clone());
                    self.stack.push(Rc::clone(&value));

                    let mut upvalues = vec![];
                    for _ in 0..upvalue_count {
                        let opcode = chunk.borrow().codes[frame.borrow().ip];
                        match opcode {
                            OpCode::Upvalue(upvalue) => {
                                upvalues.push(upvalue);
                                frame.borrow_mut().ip += 1;
                            }
                            _ => panic!("Expected Upvalue, got {opcode:?}"),
                        }
                    }

                    match value.as_ref() {
                        Value::Closure(closure) => {
                            for upvalue in upvalues {
                                if upvalue.is_local {
                                    let value = Rc::clone(
                                        &self.stack[frame.borrow().stack_offset + upvalue.index],
                                    );
                                    closure
                                        .borrow_mut()
                                        .upvalues
                                        .push(self.capture_upvalue(value));
                                } else {
                                    closure.borrow_mut().upvalues.push(Rc::clone(
                                        &frame.borrow().closure.borrow().upvalues[index],
                                    ));
                                }
                            }
                        }
                        _ => panic!("Expected Closure, got {value:?}"),
                    }
                }
                OpCode::Upvalue(_) => unreachable!(),
                OpCode::CloseUpvalue => {
                    self.close_upvalues(self.stack.last().cloned().unwrap());
                    self.stack.pop();
                }
                OpCode::Return => {
                    let result = self.stack.pop().unwrap();
                    let value = self
                        .stack
                        .get(frame.borrow().stack_offset)
                        .cloned()
                        .unwrap();
                    self.close_upvalues(value);

                    self.frames.pop();
                    if self.frames.is_empty() {
                        self.stack.pop();
                        return Ok(());
                    }
                    self.stack.truncate(frame.borrow().stack_offset);
                    self.stack.push(result);
                    frame = Rc::clone(self.frames.last().unwrap());
                    chunk = Rc::clone(&frame.borrow().closure.borrow().function.chunk);
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
                    let value = Rc::clone(&self.stack[slot + 1]);
                    self.stack[slot] = value;
                }
                OpCode::GetGlobal(slot) => {
                    let name = chunk.borrow().read_constant(slot).name().unwrap();
                    if let Some(variable) = self.globals.get(&name) {
                        self.stack.push(Rc::clone(variable));
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
                OpCode::GetUpvalue(slot) => {
                    let value = Rc::clone(
                        &frame.borrow().closure.borrow().upvalues[slot]
                            .borrow()
                            .location,
                    );
                    self.stack.push(value);
                }
                OpCode::SetUpvalue(slot) => {
                    let value = Rc::clone(self.stack.last().unwrap());
                    frame.borrow().closure.borrow().upvalues[slot]
                        .borrow_mut()
                        .location = value;
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
                OpCode::Class(index) => {
                    let name = chunk.borrow().read_constant(index).name().unwrap();
                    let class = Rc::new(Value::Class(Rc::new(RefCell::new(ObjClass::new(name)))));
                    self.stack.push(class);
                }
            }
        }
    }

    fn call(&mut self, closure: BoxedObjClosure, arg_count: usize) -> Result<()> {
        let arity = closure.borrow().function.arity;
        if arg_count > arity {
            return Err(
                self.runtime_error(format!("Expected {} arguments but got {arg_count}.", arity))
            );
        }

        if self.frames.len() == FRAMES_MAX {
            return Err(self.runtime_error("Stack overflow."));
        }

        let stack_offset = self.stack.len() - arg_count - 1;
        let frame = Rc::new(RefCell::new(CallFrame::new(closure, stack_offset)));
        self.frames.push(frame);
        Ok(())
    }

    fn call_value(&mut self, callee: Rc<Value>, arg_count: usize) -> Result<()> {
        match callee.as_ref() {
            Value::Closure(closure) => self.call(Rc::clone(closure), arg_count),
            Value::ObjNative(native) => {
                let stack_len = self.stack.len();
                let args = &mut self.stack.as_mut_slice()[stack_len - arg_count..stack_len];
                match (native.function)(args) {
                    Ok(result) => {
                        for _ in 0..arg_count + 1 {
                            self.stack.pop();
                        }
                        if let Some(result_value) = result {
                            self.stack.push(Rc::new(result_value))
                        }
                        Ok(())
                    }
                    Err(error) => Err(self.runtime_error(error.to_string())),
                }
            }
            _ => Err(self.runtime_error("Can only call functions and classes.")),
        }
    }

    fn capture_upvalue(&mut self, local: BoxedValue) -> BoxedObjUpvalue {
        let mut prev_upvalue: Option<BoxedObjUpvalue> = None;
        let mut upvalue = self.head_open_upvalue.as_ref().cloned();

        while upvalue
            .as_ref()
            .is_some_and(|x| Rc::as_ptr(&x.borrow().location) > Rc::as_ptr(&local))
        {
            prev_upvalue = upvalue.as_ref().cloned();
            upvalue = upvalue.unwrap().borrow().next.as_ref().cloned();
        }

        if let Some(this_upvalue) = upvalue.as_ref().cloned() {
            if this_upvalue.borrow().location == local {
                return this_upvalue;
            }
        }

        let mut created_upvalue = ObjUpvalue::new(local);
        created_upvalue.next = upvalue;
        let created_upvalue = Rc::new(RefCell::new(created_upvalue));

        if let Some(prev_upvalue) = prev_upvalue {
            prev_upvalue.borrow_mut().next = Some(Rc::clone(&created_upvalue));
        } else {
            self.head_open_upvalue = Some(Rc::clone(&created_upvalue));
        }

        created_upvalue
    }

    fn close_upvalues(&mut self, last: BoxedValue) {
        while self
            .head_open_upvalue
            .as_ref()
            .is_some_and(|x| Rc::as_ptr(&x.borrow().location) >= Rc::as_ptr(&last))
        {
            let upvalue = self.head_open_upvalue.as_ref().cloned().unwrap();
            let mut upvalue = upvalue.borrow_mut();
            upvalue.closed = Rc::clone(&upvalue.location);
            upvalue.location = Rc::clone(&upvalue.closed);
            self.head_open_upvalue = upvalue.next.as_ref().cloned();
        }
    }

    fn runtime_error(&self, msg: impl fmt::Display) -> InterpretError {
        let mut full_msg = format!("{msg}\n");
        for frame in self.frames.iter() {
            let frame = frame.borrow();
            let function = &frame.closure.borrow().function;
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

fn clock_native(_args: &mut [BoxedValue]) -> NativeFnResult {
    Ok(Some(
        SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_secs_f64()
            .into(),
    ))
}

fn refcount_native(args: &mut [BoxedValue]) -> NativeFnResult {
    if let Some(value) = args.first() {
        let strong_count = u32::try_from(Rc::strong_count(value))?;
        Ok(Some(f64::from(strong_count).into()))
    } else {
        Err("This function takes one argument".into())
    }
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
