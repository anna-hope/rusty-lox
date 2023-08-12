use crate::value::Value;
use std::fmt::{Display, Formatter};

#[derive(Debug, Copy, Clone)]
pub enum OpCode {
    Constant(usize),
    Add,
    Subtract,
    Multiply,
    Divide,
    Negate,
    Return,
}

impl Display for OpCode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let debug_repr = format!("{self:?}");
        let display_repr =
            format!("OP_{}", debug_repr.to_ascii_uppercase()).replace(r"\(\d+\)", "");
        write!(f, "{display_repr}")
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

    pub fn read_constant(&self, index: usize) -> Value {
        self.constants[index]
    }

    pub fn disassemble_instruction(&self, offset: usize) -> usize {
        print!("{:04} ", offset);
        if offset > 0 && self.lines[offset] == self.lines[offset - 1] {
            print!("   | ");
        } else {
            print!("{:4} ", self.lines[offset]);
        }

        let instruction = self.codes[offset];
        match instruction {
            OpCode::Return => {
                println!("{instruction}");
                offset + 1
            }
            OpCode::Constant(index) => {
                let value = self.constants[index];
                println!("{instruction:-16} {index:4} '{value}'");
                offset + 1
            }
            OpCode::Add | OpCode::Subtract | OpCode::Multiply | OpCode::Divide => {
                println!("{instruction}");
                offset + 1
            }
            OpCode::Negate => {
                println!("{instruction}");
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

impl<'iterator> IntoIterator for &'iterator Chunk {
    type Item = OpCode;
    type IntoIter = ChunkIterator<'iterator>;

    fn into_iter(self) -> Self::IntoIter {
        ChunkIterator {
            codes: &self.codes,
            index: 0,
        }
    }
}

pub struct ChunkIterator<'a> {
    codes: &'a Vec<OpCode>,
    index: usize,
}

impl<'a> Iterator for ChunkIterator<'a> {
    type Item = OpCode;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.codes.len() {
            let code = self.codes[self.index];
            self.index += 1;
            Some(code)
        } else {
            None
        }
    }
}
