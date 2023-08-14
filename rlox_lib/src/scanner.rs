use std::collections::HashMap;

use crate::scanner::TokenType::Eof;
use lazy_static::lazy_static;
use thiserror::Error;

lazy_static! {
    static ref KEYWORDS: HashMap<String, TokenType> = {
        let mut keywords = HashMap::new();

        keywords.insert("and".to_string(), TokenType::And);
        keywords.insert("class".to_string(), TokenType::Class);
        keywords.insert("else".to_string(), TokenType::Else);
        keywords.insert("if".to_string(), TokenType::If);
        keywords.insert("nil".to_string(), TokenType::Nil);
        keywords.insert("or".to_string(), TokenType::Or);
        keywords.insert("print".to_string(), TokenType::Print);
        keywords.insert("return".to_string(), TokenType::Return);
        keywords.insert("super".to_string(), TokenType::Super);
        keywords.insert("var".to_string(), TokenType::Var);
        keywords.insert("while".to_string(), TokenType::While);

        keywords.insert("false".to_string(), TokenType::False);
        keywords.insert("for".to_string(), TokenType::For);
        keywords.insert("fun".to_string(), TokenType::Fun);

        keywords.insert("this".to_string(), TokenType::This);
        keywords.insert("true".to_string(), TokenType::True);

        keywords
    };
}

macro_rules! matches {
    ($char_iter:expr, $expected:literal, $primary:expr, $alternative:expr, $index:expr) => {
        if let Some((_, c)) = $char_iter.peek() {
            if c == &$expected {
                $char_iter.next();
                $index += 1;
                $primary
            } else {
                $alternative
            }
        } else {
            $alternative
        }
    };
}

pub struct Scanner {
    source: String,
}

impl Scanner {
    pub fn new(source: String) -> Self {
        Self { source }
    }

    pub fn scan_tokens(&self) -> Vec<Token> {
        let mut tokens = vec![];
        let mut previous = 0;
        let mut line = 1;

        let mut char_iter = self.source.chars().enumerate().peekable();

        while let Some((mut index, c)) = char_iter.next() {
            // Skip whitespace.
            if c == '\n' {
                line += 1;
            }

            if c.is_ascii_whitespace() {
                // Increment previous because we are ignoring whitespace,
                // so previous should start when the whitespace ends.
                previous += 1;
            } else if c == '/' {
                if let Some((_, c_next)) = char_iter.peek() {
                    if c_next == &'/' {
                        // A comment goes until the end of the line.
                        for (_, c1) in char_iter.by_ref() {
                            if c1 == '\n' {
                                break;
                            }

                            // Increment previous and index,
                            // because both should start when the comment ends.
                            previous += 1;
                            index += 1;
                        }
                    }
                }
            } else if is_alpha(c) {
                // Gather characters into a string so we can check it against
                // the map of keywords.
                let mut string_so_far = String::new();
                string_so_far.push(c);

                // We need to iterate while peeking because it's the only way
                // to iterate over the token without also consuming what follows.
                while let Some((_, c1)) = char_iter.peek() {
                    if is_alpha(*c1) || c1.is_ascii_digit() {
                        string_so_far.push(*c1);
                        index += 1;
                        char_iter.next();
                    } else {
                        break;
                    }
                }

                let token_type = if let Some(token_type) = KEYWORDS.get(&string_so_far) {
                    token_type.to_owned()
                } else {
                    TokenType::Identifier
                };

                let length = index - previous + 1;
                let token = Token::new(token_type, previous, length, line);
                tokens.push(token);
                previous += length;
            } else if c.is_ascii_digit() {
                // Consume the whole number, while advancing the main iterator.
                // Numbers can be fractional, like 123.45.
                while let Some((_, c1)) = char_iter.peek() {
                    // Look for a fractional part.
                    if c1 == &'.' {
                        if let Some((_, c_next)) = char_iter.peek() {
                            if c_next.is_ascii_digit() {
                                // Consume the ".".
                                char_iter.next();
                                index += 1;
                            }
                        }

                        // Go to the next digit.
                        index += 1;
                        char_iter.next();
                    } else if c1.is_ascii_digit() {
                        index += 1;
                        char_iter.next();
                    } else {
                        break;
                    }
                }

                let length = index - previous + 1;
                let token = Token::new(TokenType::Number, previous, length, line);
                tokens.push(token);
                previous += length;
            } else {
                let token_type = match c {
                    '(' => TokenType::LeftParen,
                    ')' => TokenType::RightParen,
                    '{' => TokenType::LeftBrace,
                    '}' => TokenType::RightBrace,
                    ';' => TokenType::Semicolon,
                    ',' => TokenType::Comma,
                    '.' => TokenType::Dot,
                    '-' => TokenType::Minus,
                    '+' => TokenType::Plus,
                    '/' => TokenType::Slash,
                    '*' => TokenType::Star,
                    '!' => {
                        matches!(char_iter, '=', TokenType::BangEqual, TokenType::Bang, index)
                    }
                    '=' => {
                        matches!(
                            char_iter,
                            '=',
                            TokenType::EqualEqual,
                            TokenType::Equal,
                            index
                        )
                    }
                    '<' => {
                        matches!(char_iter, '=', TokenType::LessEqual, TokenType::Less, index)
                    }
                    '>' => {
                        matches!(
                            char_iter,
                            '=',
                            TokenType::GreaterEqual,
                            TokenType::Greater,
                            index
                        )
                    }
                    '"' => {
                        while let Some((_, c1)) = char_iter.peek() {
                            if c1 == &'"' {
                                break;
                            }

                            if let Some((_, next_char)) = char_iter.peek() {
                                if next_char == &'\n' {
                                    line += 1;
                                }
                            }

                            char_iter.next();
                            index += 1;
                        }

                        if char_iter.peek().is_none() {
                            TokenType::Error(ScannerError::UnterminatedString(line))
                        } else {
                            char_iter.next();
                            index += 1;
                            TokenType::String
                        }
                    }
                    _ => TokenType::Error(ScannerError::UnexpectedCharacter(line)),
                };

                let length = index - previous + 1;
                let token = Token::new(token_type, previous, length, line);
                tokens.push(token);
                previous += length;
            }
        }

        let eof = Token::new(Eof, previous, 0, line);
        tokens.push(eof);
        tokens
    }
}

fn is_alpha(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

#[derive(Debug, Clone, Copy)]
pub struct Token {
    pub token_type: TokenType,
    pub start: usize,
    pub length: usize,
    pub line: usize,
}

impl Token {
    pub fn new(token_type: TokenType, start: usize, length: usize, line: usize) -> Self {
        Self {
            token_type,
            start,
            length,
            line,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum TokenType {
    // Single-character tokens.
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,

    // One or two character tokens.
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    // Literals.
    Identifier,
    String,
    Number,

    // Keywords.
    And,
    Class,
    Else,
    False,
    For,
    Fun,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,

    Error(ScannerError),
    Eof,
}

#[derive(Debug, Error, Clone, Copy, Eq, PartialEq)]
pub enum ScannerError {
    #[error("Unexpected character at line {0}")]
    UnexpectedCharacter(usize),

    #[error("Unterminated string at line {0}")]
    UnterminatedString(usize),
}
