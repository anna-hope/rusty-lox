use crate::value::Value;
use std::fmt::{Display, Formatter};

type JumpOffset = usize;
type StackSlot = usize;

#[derive(Debug, Copy, Clone)]
pub enum OpCode {
    Constant(usize),
    Nil,
    True,
    False,
    Pop,
    GetLocal(StackSlot),
    SetLocal(StackSlot),
    GetGlobal(StackSlot),
    DefineGlobal(StackSlot),
    SetGlobal(StackSlot),
    Equal,
    Greater,
    Less,
    Add,
    Subtract,
    Multiply,
    Divide,
    Not,
    Negate,
    Print,
    Jump(JumpOffset),
    JumpIfFalse(JumpOffset),
    Loop(JumpOffset),
    Return,
}

impl Display for OpCode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let debug_repr = format!("{self:?}");
        let display_repr = format!("OP_{}", debug_repr);
        write!(f, "{display_repr}")
    }
}

#[derive(Debug, Clone)]
pub struct Chunk {
    pub codes: Vec<OpCode>,
    pub lines: Vec<usize>,
    constants: Vec<Value>,
}

impl Chunk {
    pub fn new() -> Self {
        Chunk {
            codes: vec![],
            lines: vec![],
            constants: vec![],
        }
    }

    pub fn len(&self) -> usize {
        self.codes.len()
    }

    pub fn add_code(&mut self, code: OpCode, line: usize) {
        self.codes.push(code);
        self.lines.push(line);
    }

    /// Pushes a value to the constant store, returning its index.
    pub fn push_constant(&mut self, value: Value) -> usize {
        self.constants.push(value);
        self.constants.len() - 1
    }

    /// Pushes a value to the constants store and adds a code
    /// wrapping its index to the chunk.
    /// This method calls [Self::push_constant] internally,
    /// therefore that method should not be called before this one for the same value.
    pub fn add_constant_code(&mut self, value: Value, line: usize) {
        let index = self.push_constant(value);
        self.add_code(OpCode::Constant(index), line);
    }

    pub fn read_constant(&self, index: usize) -> &Value {
        &self.constants[index]
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
            OpCode::Constant(index)
            | OpCode::DefineGlobal(index)
            | OpCode::GetGlobal(index)
            | OpCode::SetGlobal(index) => {
                let value = &self.constants[index];
                println!("{instruction:-16} {index:4} '{value:?}'");
            }
            OpCode::GetLocal(index) | OpCode::SetLocal(index) => {
                println!("{instruction:-16} {index:4}");
            }
            OpCode::Jump(jump_offset) | OpCode::JumpIfFalse(jump_offset) => {
                println!(
                    "{instruction:-16} {offset:4} -> {}",
                    offset + 1 + jump_offset
                );
            }
            OpCode::Loop(jump_offset) => {
                println!(
                    "{instruction:-16} {offset:4} -> {}",
                    offset + 1 - jump_offset
                );
            }
            _ => {
                println!("{instruction}");
            }
        }

        offset + 1
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
