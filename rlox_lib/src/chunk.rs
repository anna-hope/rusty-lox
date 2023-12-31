use std::fmt::{Display, Formatter};

use crate::value::Value;

type JumpOffset = usize;
type ConstantIndex = usize;

#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub(crate) struct Upvalue {
    pub index: usize,
    pub is_local: bool,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub(crate) enum OpCode {
    Constant(ConstantIndex),
    Nil,
    True,
    False,
    Pop,
    GetLocal(ConstantIndex),
    SetLocal(ConstantIndex),
    GetGlobal(ConstantIndex),
    DefineGlobal(ConstantIndex),
    SetGlobal(ConstantIndex),
    GetUpvalue(ConstantIndex),
    SetUpvalue(ConstantIndex),
    GetProperty(ConstantIndex),
    SetProperty(ConstantIndex),
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
    Call(usize),
    Invoke(usize, usize),
    Closure(usize, usize),
    Upvalue(Upvalue),
    CloseUpvalue,
    Return,
    Class(ConstantIndex),
    Method(ConstantIndex),
}

impl Display for OpCode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let debug_repr = format!("{self:?}");
        let variant_repr = debug_repr.split('(').next().unwrap();

        let mut op_repr = String::new();
        let mut iter = variant_repr.chars().peekable();
        while let Some(c) = iter.next() {
            op_repr.push(c.to_ascii_uppercase());
            if let Some(next_c) = iter.peek() {
                if next_c.is_ascii_uppercase() {
                    op_repr.push('_');
                }
            }
        }

        let display_repr = format!("OP_{}", op_repr);
        write!(f, "{display_repr}")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Chunk {
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

    pub fn add_closure(&mut self, value: Value, line: usize, upvalues: &[Upvalue]) {
        let index = self.push_constant(value);
        self.add_code(OpCode::Closure(index, upvalues.len()), line);
        for upvalue in upvalues {
            self.add_code(OpCode::Upvalue(*upvalue), line);
        }
    }

    pub fn read_constant(&self, index: usize) -> &Value {
        &self.constants[index]
    }

    pub fn disassemble_instruction(&self, offset: usize) {
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
            | OpCode::SetGlobal(index)
            | OpCode::GetProperty(index)
            | OpCode::SetProperty(index)
            | OpCode::Method(index) => {
                let value = &self.constants[index];
                println!("{instruction:-16} {index:4} '{value:?}'");
            }
            OpCode::GetUpvalue(index) | OpCode::SetUpvalue(index) => {
                println!("{instruction:-16} {index:4}");
            }
            OpCode::Closure(index, upvalue_count) => {
                let function = &self.constants[index];
                println!("{instruction:-16} {function:4} {upvalue_count:4} upvalues");
            }
            OpCode::Upvalue(upvalue) => {
                println!("{instruction:-16} {upvalue:?}");
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
            OpCode::Call(arg_count) => {
                println!("{instruction:-16} {arg_count:4}");
            }
            OpCode::Invoke(constant_index, arg_count) => {
                let constant = &self.constants[constant_index];
                println!("{instruction:-16} ({arg_count} args) {constant_index:4} {constant}");
            }
            _ => {
                println!("{instruction}");
            }
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
