use std::ops::Add;
use std::{env, mem};

use thiserror::Error;

use crate::chunk::OpCode::Divide;
use crate::chunk::{Chunk, OpCode};
use crate::scanner::{Scanner, Token, TokenType};
use crate::value::Value;

#[derive(Debug, Error)]
pub enum CompileError {
    #[error("Compile error")]
    Error,
}

pub type Result<T> = std::result::Result<T, CompileError>;

#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialOrd, PartialEq)]
enum Precedence {
    Lowest,
    Assignment, // =
    Or,         // or
    And,        // and
    Equality,   // == !=
    Comparison, // < > <= >=
    Term,       // + -
    Factor,     // * /
    Unary,      // ! -
    Call,       // . ()
    Primary,
}

impl Add<u8> for Precedence {
    type Output = Self;

    fn add(self, rhs: u8) -> Self::Output {
        let discriminator = self as u8;
        let max_discriminator = Self::Primary as u8;
        let sum = discriminator + rhs;
        if sum > max_discriminator {
            Self::Primary
        } else {
            // SAFETY: because we check that self + rhs <= max_discriminator,
            // it's safe to transmute the sum back into Precedence.
            unsafe { mem::transmute::<u8, Self>(sum) }
        }
    }
}

impl From<TokenType> for Precedence {
    fn from(value: TokenType) -> Self {
        match value {
            TokenType::LeftParen | TokenType::RightParen => Precedence::Lowest,
            TokenType::LeftBrace | TokenType::RightBrace => Precedence::Lowest,
            TokenType::Comma => Precedence::Lowest,
            TokenType::Dot => Precedence::Lowest,
            TokenType::Minus | TokenType::Plus => Precedence::Term,
            TokenType::Semicolon => Precedence::Lowest,
            TokenType::Slash | TokenType::Star => Precedence::Factor,
            TokenType::BangEqual => Precedence::Equality,
            TokenType::EqualEqual => Precedence::Equality,
            TokenType::Greater
            | TokenType::GreaterEqual
            | TokenType::Less
            | TokenType::LessEqual => Precedence::Comparison,
            _ => Precedence::Lowest,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Parser {
    scanner: Scanner,
    previous: Option<Token>,
    current: Option<Token>,
    chunk: Chunk,
    had_error: bool,
    panic_mode: bool,
}

impl Parser {
    pub fn new(source: impl ToString) -> Self {
        let scanner = Scanner::new(source);
        Self {
            scanner,
            previous: None,
            current: None,
            chunk: Chunk::new(),
            had_error: false,
            panic_mode: false,
        }
    }

    pub fn compile(&mut self) -> Result<Vec<Chunk>> {
        self.advance();
        self.expression();
        self.consume(TokenType::Eof, "Expect end of expression");
        self.end_compiler();

        let chunks = vec![self.chunk.clone()];

        if self.had_error {
            Err(CompileError::Error)
        } else {
            Ok(chunks)
        }
    }

    fn advance(&mut self) {
        self.previous = self.current.clone();
        loop {
            self.current = Some(self.scanner.scan_token());
            if !matches!(
                self.current.as_ref().unwrap().token_type,
                TokenType::Error(_)
            ) {
                break;
            }

            self.error_at_current(self.current.as_ref().unwrap().value.clone().as_str());
        }
    }

    fn error_at_current(&mut self, message: &str) {
        self.error_at(self.current.as_ref().unwrap(), message);
        self.panic_mode = true;
        self.had_error = true;
    }

    fn error_at_previous(&mut self, message: &str) {
        self.error_at(self.previous.as_ref().unwrap(), message);
        self.panic_mode = true;
        self.had_error = true;
    }

    fn error_at(&self, token: &Token, message: &str) {
        if self.panic_mode {
            return;
        }

        eprint!("[line {}] Error", token.line);
        match token.token_type {
            TokenType::Eof => eprint!(" at end"),
            TokenType::Error(_) => {
                // Nothing here.
            }
            _ => eprint!(" at {}: {}", token.start, token.value),
        }

        eprintln!(": {}", message);
    }

    fn consume(&mut self, token_type: TokenType, message: &str) {
        if self.current.as_ref().unwrap().token_type == token_type {
            self.advance();
        } else {
            self.error_at_current(message);
        }
    }

    fn emit_code(&mut self, code: OpCode) {
        self.chunk
            .add_code(code, self.previous.as_ref().unwrap().line);
    }

    fn emit_codes(&mut self, code1: OpCode, code2: OpCode) {
        // Not sure if we'll use this method this way,
        // but it's defined this way in the book so we'll keep it like this for now.
        self.emit_code(code1);
        self.emit_code(code2);
    }

    fn end_compiler(&mut self) {
        self.emit_return();
        if env::var("DEBUG_PRINT_CODE") == Ok("1".to_string()) && !self.had_error {
            self.chunk.disassemble("code");
        }
    }

    fn binary(&mut self) {
        let operator_type = self.previous.as_ref().unwrap().token_type;
        let precedence: Precedence = operator_type.into();
        self.parse_precedence(precedence + 1);

        match operator_type {
            TokenType::Plus => self.emit_code(OpCode::Add),
            TokenType::Minus => self.emit_code(OpCode::Subtract),
            TokenType::Star => self.emit_code(OpCode::Multiply),
            TokenType::Slash => self.emit_code(Divide),
            TokenType::BangEqual => self.emit_codes(OpCode::Equal, OpCode::Not),
            TokenType::EqualEqual => self.emit_code(OpCode::Equal),
            TokenType::Greater => self.emit_code(OpCode::Greater),
            TokenType::GreaterEqual => self.emit_codes(OpCode::Less, OpCode::Not),
            TokenType::Less => self.emit_code(OpCode::Less),
            TokenType::LessEqual => self.emit_codes(OpCode::Greater, OpCode::Not),
            _ => unreachable!(),
        }
    }

    fn literal(&mut self) {
        let previous_type = self.previous.as_ref().unwrap().token_type;

        match previous_type {
            TokenType::False => self.emit_code(OpCode::False),
            TokenType::Nil => self.emit_code(OpCode::Nil),
            TokenType::True => self.emit_code(OpCode::True),
            _ => unreachable!(),
        }
    }

    fn grouping(&mut self) {
        self.expression();
        self.consume(TokenType::RightParen, "Expect ')' after expression.");
    }

    fn number(&mut self) {
        let value = self
            .previous
            .as_ref()
            .unwrap()
            .value
            .parse::<f64>()
            .unwrap();
        self.emit_constant(value.into());
    }

    fn string(&mut self) {
        let string = self.previous.as_ref().unwrap().value.clone();
        self.emit_constant(string.into());
    }

    fn unary(&mut self) {
        let operator_type = self.previous.as_ref().unwrap().token_type;

        // Compile the operand.
        self.parse_precedence(Precedence::Unary);

        // Emit the operator instruction.
        match operator_type {
            TokenType::Minus => self.emit_code(OpCode::Negate),
            TokenType::Bang => self.emit_code(OpCode::Not),
            _ => unreachable!(),
        }
    }

    fn get_prefix_rule(&self) -> Option<fn(&mut Parser)> {
        match self.previous.as_ref().unwrap().token_type {
            TokenType::LeftParen => Some(Self::grouping),
            TokenType::Minus => Some(Self::unary),
            TokenType::Number => Some(Self::number),
            TokenType::False | TokenType::True | TokenType::Nil => Some(Self::literal),
            TokenType::Bang => Some(Self::unary),
            TokenType::String => Some(Self::string),
            _ => None,
        }
    }

    fn get_infix_rule(&self) -> Option<fn(&mut Parser)> {
        match self.previous.as_ref().unwrap().token_type {
            TokenType::Minus | TokenType::Plus => Some(Self::binary),
            TokenType::Slash | TokenType::Star => Some(Self::binary),
            TokenType::BangEqual => Some(Self::binary),
            TokenType::EqualEqual => Some(Self::binary),
            TokenType::Greater | TokenType::GreaterEqual => Some(Self::binary),
            TokenType::Less | TokenType::LessEqual => Some(Self::binary),
            _ => None,
        }
    }

    fn parse_precedence(&mut self, precedence: Precedence) {
        self.advance();

        if let Some(prefix_rule) = self.get_prefix_rule() {
            prefix_rule(self);

            while precedence <= self.current.as_ref().unwrap().token_type.into() {
                self.advance();
                let infix_rule = self.get_infix_rule().unwrap_or_else(|| {
                    panic!(
                        "Expected an infix rule for {:?}",
                        self.previous.as_ref().unwrap().token_type
                    )
                });
                infix_rule(self);
            }
        } else {
            self.error_at_previous("Expect expression");
        }
    }

    fn expression(&mut self) {
        self.parse_precedence(Precedence::Assignment);
    }

    fn emit_return(&mut self) {
        self.emit_code(OpCode::Return);
    }

    fn emit_constant(&mut self, value: Value) {
        self.chunk
            .add_constant(value, self.previous.as_ref().unwrap().line);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_arithmetic_expression() {
        let input = "1 + 1";
        let mut parser = Parser::new(input);
        let chunks = parser.compile().unwrap();

        for chunk in chunks.iter() {
            for index in 0..chunk.codes.len() {
                chunk.disassemble_instruction(index);
            }
        }
    }
}
