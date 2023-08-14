use std::env;
use std::ops::{Add, Div, Mul, Sub};

use thiserror::Error;

use crate::{
    chunk::{Chunk, OpCode},
    compiler::compile,
    value::Value,
};

pub type Result<T> = std::result::Result<T, InterpretError>;

macro_rules! binary_op {
    ($op:expr, $stack:expr) => {
        let b = $stack.pop().unwrap();
        let a = $stack.pop().unwrap();
        $stack.push($op(a, b));
    };
}

pub struct VM {
    stack: Vec<Value>,
}

impl VM {
    pub fn new() -> Self {
        Self {
            stack: Vec::with_capacity(256),
        }
    }

    pub fn interpret(&self, source: String) -> Result<()> {
        compile(source);
        Ok(())

        // for (offset, code) in chunk.into_iter().enumerate() {
        //     if env::var("DEBUG_TRACE_EXECUTION") == Ok("1".to_string()) {
        //         dbg!(&self.stack);
        //         chunk.disassemble_instruction(offset);
        //     }

        //     match code {
        //         OpCode::Constant(index) => {
        //             let constant = chunk.read_constant(index);
        //             self.stack.push(constant);
        //             println!("{constant}");
        //         }
        //         OpCode::Negate => {
        //             let value = self.stack.pop().expect("Expect a value on the stack");
        //             self.stack.push(-value);
        //         }
        //         OpCode::Add => {
        //             binary_op!(Add::add, self.stack);
        //         }
        //         OpCode::Subtract => {
        //             binary_op!(Sub::sub, self.stack);
        //         }
        //         OpCode::Multiply => {
        //             binary_op!(Mul::mul, self.stack);
        //         }
        //         OpCode::Divide => {
        //             binary_op!(Div::div, self.stack);
        //         }
        //         OpCode::Return => {
        //             if let Some(value) = self.stack.pop() {
        //                 println!("{value}");
        //             }

        //             return Ok(());
        //         }
        //     }
        // }
        // Ok(())
    }
}

#[derive(Debug, Error)]
pub enum InterpretError {
    #[error("Compile error")]
    Compile,

    #[error("Runtime error")]
    Runtime,
}
