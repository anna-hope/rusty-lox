use crate::value::Value;
use std::fmt::{Display, Formatter};

#[derive(Debug, Copy, Clone)]
pub enum OpCode {
    OpConstant(usize),
    OpReturn,
}

impl Display for OpCode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug)]
pub struct Chunk {
    codes: Vec<OpCode>,
    lines: Vec<usize>,
    constants: Vec<f64>,
}

impl Chunk {
    pub fn new() -> Self {
        Chunk {
            codes: vec![],
            lines: vec![],
            constants: vec![],
        }
    }

    pub fn add_code(&mut self, code: OpCode, line: usize) {
        self.codes.push(code);
        self.lines.push(line);
    }

    pub fn add_constant(&mut self, value: Value) -> usize {
        self.constants.push(value);
        self.constants.len() - 1
    }

    fn disassemble_instruction(&self, offset: usize) -> usize {
        print!("{:04} ", offset);
        if offset > 0 && self.lines[offset] == self.lines[offset - 1] {
            print!("   | ");
        } else {
            print!("{:4} ", self.lines[offset]);
        }

        let instruction = self.codes[offset];
        match instruction {
            OpCode::OpReturn => {
                println!("{instruction}");
                offset + 1
            }
            OpCode::OpConstant(index) => {
                let value = self.constants[index];
                println!("{instruction:-16} {index:4} '{value}'");
                offset + 1
            } // _ => {
              //     println!("Unknown opcode: {instruction:?}");
              //     offset + 1
              // }
        }
    }

    pub fn disassemble(&self, name: &str) {
        println!("== {name} ==");

        for i in 0..self.codes.len() {
            self.disassemble_instruction(i);
        }
    }
}

impl Default for Chunk {
    fn default() -> Self {
        Self::new()
    }
}
