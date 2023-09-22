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

        while !self.match_token(TokenType::Eof) {
            self.declaration();
        }

        self.end_compiler();

        let chunks = vec![self.chunk.clone()];

        if self.had_error {
            Err(CompileError::Error)
        } else {
            Ok(chunks)
        }
    }

    fn advance(&mut self) {
        self.previous = self.current;
        loop {
            self.current = Some(self.scanner.scan_token());
            if !matches!(self.current.unwrap().token_type, TokenType::Error(_)) {
                break;
            }

            self.error_at_current(self.current.unwrap().value.as_str());
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

    fn check(&self, token_type: TokenType) -> bool {
        self.current.unwrap().token_type == token_type
    }

    fn match_token(&mut self, token_type: TokenType) -> bool {
        if !self.check(token_type) {
            return false;
        }
        self.advance();
        true
    }

    fn emit_code(&mut self, code: OpCode) {
        self.chunk.add_code(code, self.previous.unwrap().line);
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
        let operator_type = self.previous.unwrap().token_type;
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

    fn literal(&mut self, _can_assign: bool) {
        let previous_type = self.previous.as_ref().unwrap().token_type;

        match previous_type {
            TokenType::False => self.emit_code(OpCode::False),
            TokenType::Nil => self.emit_code(OpCode::Nil),
            TokenType::True => self.emit_code(OpCode::True),
            _ => unreachable!(),
        }
    }

    fn grouping(&mut self, _can_assign: bool) {
        self.expression();
        self.consume(TokenType::RightParen, "Expect ')' after expression.");
    }

    fn number(&mut self, _can_assign: bool) {
        let value = self
            .previous
            .as_ref()
            .unwrap()
            .value
            .parse::<f64>()
            .unwrap();
        self.emit_constant(value.into());
    }

    fn string(&mut self, _can_assign: bool) {
        let string = self.previous.unwrap().value;
        self.emit_constant(string.into());
    }

    fn named_variable(&mut self, name: Token, can_assign: bool) {
        let arg = self.identifier_constant(name);

        if can_assign && self.match_token(TokenType::Equal) {
            self.expression();
            self.emit_code(OpCode::SetGlobal(arg));
        } else {
            self.emit_code(OpCode::GetGlobal(arg));
        }
    }

    fn variable(&mut self, can_assign: bool) {
        self.named_variable(self.previous.unwrap(), can_assign);
    }

    fn unary(&mut self, _can_assign: bool) {
        let operator_type = self.previous.unwrap().token_type;

        // Compile the operand.
        self.parse_precedence(Precedence::Unary);

        // Emit the operator instruction.
        match operator_type {
            TokenType::Minus => self.emit_code(OpCode::Negate),
            TokenType::Bang => self.emit_code(OpCode::Not),
            _ => unreachable!(),
        }
    }

    fn get_prefix_rule(&self) -> Option<fn(&mut Parser, bool)> {
        match self.previous.as_ref().unwrap().token_type {
            TokenType::LeftParen => Some(Self::grouping),
            TokenType::Minus => Some(Self::unary),
            TokenType::Number => Some(Self::number),
            TokenType::False | TokenType::True | TokenType::Nil => Some(Self::literal),
            TokenType::Bang => Some(Self::unary),
            TokenType::String => Some(Self::string),
            TokenType::Identifier => Some(Self::variable),
            _ => todo!(),
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
            let can_assign = precedence <= Precedence::Assignment;
            prefix_rule(self, can_assign);

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

            if can_assign && self.match_token(TokenType::Equal) {
                self.error_at_previous("Invalid assignment target.");
            }
        } else {
            self.error_at_previous("Expect expression");
        }
    }

    fn identifier_constant(&mut self, name: Token) -> usize {
        self.chunk.push_constant(Value::Obj(name.value))
    }

    fn parse_variable(&mut self, error_message: &str) -> usize {
        self.consume(TokenType::Identifier, error_message);
        self.identifier_constant(self.previous.unwrap())
    }

    fn define_variable(&mut self, global_index: usize) {
        self.emit_code(OpCode::DefineGlobal(global_index));
    }

    fn expression(&mut self) {
        self.parse_precedence(Precedence::Assignment);
    }

    fn var_declaration(&mut self) {
        let global = self.parse_variable("Expect variable name.");

        if self.match_token(TokenType::Equal) {
            self.expression();
        } else {
            self.emit_code(OpCode::Nil);
        }

        self.consume(
            TokenType::Semicolon,
            "Expect ';' after variable declaration.",
        );

        self.define_variable(global);
    }

    fn expression_statement(&mut self) {
        self.expression();
        self.consume(TokenType::Semicolon, "Expect ';' after expression.");
        self.emit_code(OpCode::Pop);
    }

    fn print_statement(&mut self) {
        self.expression();
        self.consume(TokenType::Semicolon, "Expect ';' after value.");
        self.emit_code(OpCode::Print);
    }

    fn synchronize(&mut self) {
        self.panic_mode = false;

        while self.current.unwrap().token_type != TokenType::Eof {
            if self.previous.unwrap().token_type == TokenType::Semicolon {
                return;
            }

            match self.current.unwrap().token_type {
                TokenType::Class
                | TokenType::Fun
                | TokenType::Var
                | TokenType::For
                | TokenType::If
                | TokenType::While
                | TokenType::Print
                | TokenType::Return => {
                    return;
                }
                _ => {
                    // Do nothing.
                }
            }

            self.advance();
        }
    }

    fn declaration(&mut self) {
        if self.match_token(TokenType::Var) {
            self.var_declaration();
        } else {
            self.statement();
        }

        if self.panic_mode {
            self.synchronize();
        }
    }

    fn statement(&mut self) {
        if self.match_token(TokenType::Print) {
            self.print_statement();
        } else {
            self.expression_statement();
        }
    }

    fn emit_return(&mut self) {
        self.emit_code(OpCode::Return);
    }

    fn emit_constant(&mut self, value: Value) {
        self.chunk
            .add_constant_code(value, self.previous.unwrap().line);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_arithmetic_expression() {
        let input = "1 + 1;";
        let mut parser = Parser::new(input);
        let chunks = parser.compile().unwrap();

        for chunk in chunks.iter() {
            for index in 0..chunk.codes.len() {
                chunk.disassemble_instruction(index);
            }
        }
    }
}
