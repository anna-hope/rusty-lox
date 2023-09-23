use std::collections::hash_map::Entry;
use std::ops::{Div, Mul, Sub};
use std::{env, fmt};

use fnv::FnvHashMap;
use thiserror::Error;
use ustr::Ustr;

use crate::{
    chunk::{Chunk, OpCode},
    compiler::{Parser, ParserError},
    value::Value,
};

pub type Result<T> = std::result::Result<T, InterpretError>;

#[derive(Debug, Error)]
pub enum InterpretError {
    #[error("Compile error")]
    Compile(#[from] ParserError),

    #[error("Runtime error")]
    Runtime,
}

#[derive(Default)]
pub struct Vm {
    stack: Vec<Value>,
    line: usize,
    globals: FnvHashMap<Ustr, Value>,
    ip: usize,
}

impl Vm {
    pub fn new() -> Self {
        Self {
            stack: Vec::with_capacity(u8::MAX.into()),
            line: 0,
            globals: FnvHashMap::default(),
            ip: 0,
        }
    }

    pub fn interpret(&mut self, source: String) -> Result<Vec<Value>> {
        let mut parser = Parser::new(source);
        let chunks = parser.compile()?;
        let mut results = vec![];

        self.ip = 0;

        for chunk in chunks.iter() {
            if let Some(value) = self.run(chunk)? {
                results.push(value);
            }
        }
        Ok(results)
    }

    fn run(&mut self, chunk: &Chunk) -> Result<Option<Value>> {
        loop {
            let code = chunk.codes[self.ip];
            self.line = chunk.lines[self.ip];

            if env::var("DEBUG_TRACE_EXECUTION") == Ok("1".into()) {
                print!("          ");
                for slot in self.stack.iter() {
                    println!("[ {slot:?} ]");
                }
                chunk.disassemble_instruction(self.ip);
            }

            self.ip += 1;

            match code {
                OpCode::Print => {
                    println!("{}", self.stack.pop().unwrap());
                }
                OpCode::JumpIfFalse(slot0, slot1) => {
                    if self.stack.last().unwrap().is_falsey() {
                        self.ip = slot0;
                    } else {
                        self.ip = slot1;
                    }
                }
                OpCode::Return => return Ok(self.stack.pop()),
                OpCode::Constant(index) => {
                    let constant = chunk.read_constant(index);
                    self.stack.push(constant.clone());
                }
                OpCode::Nil => self.stack.push(Value::Nil),
                OpCode::True => self.stack.push(true.into()),
                OpCode::False => self.stack.push(false.into()),
                OpCode::Pop => {
                    self.stack.pop();
                }
                OpCode::GetLocal(slot) => {
                    let value = self.stack.get(slot).unwrap();
                    self.stack.push(value.clone());
                }
                OpCode::SetLocal(slot) => {
                    let value = self.stack.last().unwrap();
                    self.stack[slot] = value.clone();
                }
                OpCode::GetGlobal(slot) => {
                    let value = chunk.read_constant(slot);
                    let name = value.name().unwrap();
                    if let Some(variable) = self.globals.get(&name) {
                        self.stack.push(variable.clone());
                    } else {
                        self.runtime_error(format!("Undefined variable: {name}"));
                        return Err(InterpretError::Runtime);
                    }
                }
                OpCode::DefineGlobal(slot) => {
                    let value = chunk.read_constant(slot);
                    let name = value.name().unwrap();
                    self.globals
                        .insert(name, self.stack.last().unwrap().clone());
                    self.stack.pop();
                }
                OpCode::SetGlobal(slot) => {
                    let value = chunk.read_constant(slot);
                    let name = value.name().unwrap();
                    if let Entry::Occupied(mut e) = self.globals.entry(name) {
                        e.insert(self.stack.last().unwrap().clone());
                    } else {
                        self.runtime_error(format!("Undefined variable '{name}'"));
                        return Err(InterpretError::Runtime);
                    }
                }
                OpCode::Equal => {
                    let b = self.stack.pop().unwrap();
                    let a = self.stack.pop().unwrap();
                    self.stack.push((a == b).into());
                }
                OpCode::Greater => self.comparison_op(PartialOrd::gt)?,
                OpCode::Less => self.comparison_op(PartialOrd::lt)?,
                OpCode::Add => {
                    let a = self.stack.get(self.stack.len() - 2).unwrap().clone();
                    let b = self.stack.last().unwrap().clone();

                    match (a, b) {
                        (Value::String(a), Value::String(b)) => {
                            self.stack.pop();
                            self.stack.pop();
                            let a = a.replace('"', "");
                            let b = b.replace('"', "");
                            let result = format!("\"{}\"", a + b.as_str());
                            self.stack.push(result.into());
                        }
                        (Value::Number(a), Value::Number(b)) => {
                            self.stack.pop();
                            self.stack.pop();
                            self.stack.push((a + b).into());
                        }
                        _ => {
                            self.runtime_error("Operands must be two numbers or two strings.");
                            return Err(InterpretError::Runtime);
                        }
                    }
                }
                OpCode::Subtract => self.binary_op(Sub::sub)?,
                OpCode::Multiply => self.binary_op(Mul::mul)?,
                OpCode::Divide => self.binary_op(Div::div)?,
                OpCode::Not => {
                    let bool_val = self.stack.pop().unwrap().is_falsey();
                    self.stack.push(bool_val.into());
                }
                OpCode::Negate => {
                    // Inspect the value from the stack without popping it first,
                    // in case it's not a number.
                    let value = self.stack.last().unwrap().clone();

                    match value {
                        Value::Number(value) => {
                            self.stack.pop();
                            self.stack.push(Value::Number(-value))
                        }
                        _ => {
                            self.runtime_error("Operand must be a number.");
                            return Err(InterpretError::Runtime);
                        }
                    }
                }
            }
        }
    }

    fn runtime_error(&self, message: impl fmt::Display) {
        eprintln!("{message}");
        eprintln!("line {} in script", self.line);
    }

    fn binary_op<F>(&mut self, op: F) -> Result<()>
    where
        F: Fn(f64, f64) -> f64,
    {
        let b = self.stack.last().unwrap().clone();
        let a = self.stack.get(self.stack.len() - 2).unwrap().clone();

        match (a, b) {
            (Value::Number(a), Value::Number(b)) => {
                self.stack.pop();
                self.stack.pop();
                let result = op(a, b);
                self.stack.push(result.into());
            }
            _ => {
                self.runtime_error("Operands must be numbers.");
                return Err(InterpretError::Runtime);
            }
        }
        Ok(())
    }

    fn comparison_op<F>(&mut self, op: F) -> Result<()>
    where
        F: Fn(&f64, &f64) -> bool,
    {
        let b = self.stack.last().unwrap().clone();
        let a = self.stack.get(self.stack.len() - 2).unwrap().clone();

        match (a, b) {
            (Value::Number(a), Value::Number(b)) => {
                self.stack.pop();
                self.stack.pop();
                let result = op(&a, &b);
                self.stack.push(result.into());
            }
            _ => {
                self.runtime_error("Operands must be numbers.");
                return Err(InterpretError::Runtime);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evaluate_bool() {
        let input = "!(5 - 4 > 3 * 2 == !nil);";
        let mut vm = Vm::new();
        let value = &vm.interpret(input.to_string()).unwrap()[0];
        assert_eq!(value, &Value::Bool(true));
    }

    #[test]
    fn evaluate_string() {
        let input = r#"
var beverage = "cafe au lait";
var breakfast = "beignets with " + beverage;
breakfast;
"#;
        let mut vm = Vm::new();
        let result = &vm.interpret(input.to_string()).unwrap();
        dbg!(&result);
        dbg!(&vm.stack);
        // assert_eq!(value, &Value::String("beignets with cafe au lait".into()));
    }
}
