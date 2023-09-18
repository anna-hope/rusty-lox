use std::env;
use std::ops::{Add, Div, Mul, Sub};

use thiserror::Error;

use crate::{
    chunk::{Chunk, OpCode},
    compiler::{CompileError, Parser},
    value::Value,
};

pub type Result<T> = std::result::Result<T, InterpretError>;

#[derive(Debug, Error)]
pub enum InterpretError {
    #[error("Compile error")]
    Compile(#[from] CompileError),

    #[error("Runtime error")]
    Runtime,
}

macro_rules! binary_op {
    ($op:expr, $stack:expr) => {
        let b = $stack.pop().unwrap();
        let a = $stack.pop().unwrap();
        $stack.push($op(a, b));
    };
}

pub struct Vm {
    stack: Vec<Value>,
}

impl Vm {
    pub fn new() -> Self {
        Self {
            stack: Vec::with_capacity(256),
        }
    }

    pub fn interpret(&mut self, source: String) -> Result<()> {
        let mut parser = Parser::new(source);
        let chunks = parser.compile()?;
        for chunk in chunks.iter() {
            self.run(chunk)?;
        }
        Ok(())
    }

    fn run(&mut self, chunk: &Chunk) -> Result<()> {
        loop {
            for (index, code) in chunk.codes.iter().enumerate() {
                if env::var("DEBUG_TRACE_EXECUTION") == Ok("1".to_string()) {
                    print!("          ");
                    for slot in self.stack.iter() {
                        println!("[ {slot} ]")
                    }
                    chunk.disassemble_instruction(index);
                }

                match code {
                    OpCode::Return => {
                        println!("{}", self.stack.pop().unwrap());
                        return Ok(());
                    }
                    OpCode::Constant(index) => {
                        let constant = chunk.read_constant(*index);
                        self.stack.push(constant);
                    }
                    OpCode::Add => {
                        binary_op!(Add::add, self.stack);
                    }
                    OpCode::Subtract => {
                        binary_op!(Sub::sub, self.stack);
                    }
                    OpCode::Multiply => {
                        binary_op!(Mul::mul, self.stack);
                    }
                    OpCode::Divide => {
                        binary_op!(Div::div, self.stack);
                    }
                    OpCode::Negate => {
                        let value = self.stack.pop().unwrap();
                        self.stack.push(-value);
                    }
                }
            }
        }
    }
}
