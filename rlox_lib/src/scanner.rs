use std::collections::HashMap;

use lazy_static::lazy_static;
use thiserror::Error;
use ustr::Ustr;

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

#[derive(Debug, Error, Clone, Copy, Eq, PartialEq, Hash)]
pub enum ScannerError {
    #[error("Unexpected character at line {0}")]
    UnexpectedCharacter(usize),

    #[error("Unterminated string at line {0}")]
    UnterminatedString(usize),
}

#[derive(Debug, Default, Clone, Copy, Eq, PartialEq, Hash)]
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
    #[default]
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

#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Token {
    pub token_type: TokenType,
    pub start: usize,
    pub line: usize,
    pub value: Ustr,
}

impl Token {
    pub fn new(token_type: TokenType, start: usize, line: usize, value: String) -> Self {
        Self {
            token_type,
            start,
            line,
            value: Ustr::from(value.as_str()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Scanner {
    source: Vec<u8>,
    previous_index: usize,
    current_index: usize,
    current_line: usize,
}

impl Scanner {
    pub fn new(source: impl ToString) -> Self {
        Self {
            source: source.to_string().as_bytes().to_vec(),
            previous_index: 0,
            current_index: 0,
            current_line: 1,
        }
    }

    fn peek_next(&self) -> Option<char> {
        self.source
            .get(self.current_index + 1)
            .map(|x| char::from(*x))
    }

    fn peek(&self) -> Option<char> {
        self.source.get(self.current_index).map(|x| char::from(*x))
    }

    fn pick_token_type(
        &mut self,
        expected: char,
        primary: TokenType,
        alternative: TokenType,
    ) -> TokenType {
        if let Some(peeked_char) = self.peek_next() {
            if peeked_char == expected {
                self.current_index += 1;
                primary
            } else {
                alternative
            }
        } else {
            alternative
        }
    }

    fn get_source_substring(&self, start: usize, end: usize) -> String {
        // SAFETY: We know the original input is valid UTF-8 because it was a String,
        // so it's safe to rebuild a String from this slice without checking.
        unsafe { String::from_utf8_unchecked(self.source[start..end].to_vec()) }
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_ascii_whitespace() {
                self.previous_index += 1;
                self.current_index += 1;
                if c == '\n' {
                    self.current_line += 1;
                }
            } else if c == '/' {
                if let Some(next_char) = self.peek_next() {
                    if next_char == '/' {
                        while let Some(this_char) = self.peek() {
                            if this_char == '\n' {
                                break;
                            } else {
                                self.previous_index += 1;
                                self.current_index += 1;
                            }
                        }
                    } else {
                        return;
                    }
                }
            } else {
                return;
            }
        }
    }

    pub fn scan_token(&mut self) -> Token {
        self.skip_whitespace();

        if let Some(current_byte) = self.source.get(self.current_index) {
            let current_char = char::from(*current_byte);

            return if is_alpha(current_char) {
                // Gather characters into a string so we can check it against
                // the map of keywords.
                let mut string_so_far = String::new();
                string_so_far.push(current_char);

                while let Some(peeked_char) = self.peek_next() {
                    if is_alpha(peeked_char) || peeked_char.is_ascii_digit() {
                        string_so_far.push(peeked_char);
                        self.current_index += 1;
                    } else {
                        break;
                    }
                }

                let token_type = if let Some(token_type) = KEYWORDS.get(&string_so_far) {
                    token_type.to_owned()
                } else {
                    TokenType::Identifier
                };

                self.current_index += 1;
                let length = self.current_index - self.previous_index;
                let token = Token::new(
                    token_type,
                    self.previous_index,
                    self.current_line,
                    string_so_far,
                );
                self.previous_index += length;
                token
            } else if current_char.is_ascii_digit() {
                // Consume the whole number, while advancing the index.
                // Numbers can be fractional, like 123.45.

                while let Some(peeked_char) = self.peek_next() {
                    if peeked_char == '.' {
                        if let Some(next_char) = self.peek_next() {
                            if next_char.is_ascii_digit() {
                                self.current_index += 1;
                            }
                        }

                        self.current_index += 1;
                    } else if peeked_char.is_ascii_digit() {
                        self.current_index += 1;
                    } else {
                        break;
                    }
                }

                self.current_index += 1;
                let length = self.current_index - self.previous_index;
                let token_str = self.get_source_substring(self.previous_index, self.current_index);
                let token = Token::new(
                    TokenType::Number,
                    self.previous_index,
                    self.current_line,
                    token_str,
                );
                self.previous_index += length;
                token
            } else {
                let token_type = match current_char {
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
                    '!' => self.pick_token_type('=', TokenType::BangEqual, TokenType::Bang),
                    '=' => self.pick_token_type('=', TokenType::EqualEqual, TokenType::Equal),
                    '<' => self.pick_token_type('=', TokenType::LessEqual, TokenType::Less),
                    '>' => self.pick_token_type('=', TokenType::GreaterEqual, TokenType::Greater),
                    '"' => {
                        while let Some(peeked_char) = self.peek_next() {
                            if peeked_char == '"' {
                                break;
                            }

                            if peeked_char == '\n' {
                                self.current_line += 1;
                            }

                            self.current_index += 1;
                        }

                        if self.peek_next().is_none() {
                            TokenType::Error(ScannerError::UnterminatedString(self.current_line))
                        } else {
                            self.current_index += 1;
                            TokenType::String
                        }
                    }
                    _ => TokenType::Error(ScannerError::UnexpectedCharacter(self.current_line)),
                };

                self.current_index += 1;
                let length = self.current_index - self.previous_index;
                let token_substring =
                    self.get_source_substring(self.previous_index, self.current_index);
                let token = Token::new(
                    token_type,
                    self.previous_index,
                    self.current_line,
                    token_substring,
                );
                self.previous_index += length;
                token
            };
        } else {
            Token::new(
                TokenType::Eof,
                self.current_index,
                self.current_line,
                "".to_string(),
            )
        }
    }
}

fn is_alpha(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scan_tokens() {
        let inputs = ["print 1.2 + 2;", "1 / 2;"];

        let tests = [
            vec![
                Token::new(TokenType::Print, 0, 1, "print".to_string()),
                Token::new(TokenType::Number, 6, 1, "1.2".to_string()),
                Token::new(TokenType::Plus, 10, 1, "+".to_string()),
                Token::new(TokenType::Number, 12, 1, "2".to_string()),
                Token::new(TokenType::Semicolon, 13, 1, ";".to_string()),
                Token::new(TokenType::Eof, 14, 1, "".to_string()),
            ],
            vec![
                Token::new(TokenType::Number, 0, 1, "1".to_string()),
                Token::new(TokenType::Slash, 2, 1, "/".to_string()),
                Token::new(TokenType::Number, 4, 1, "2".to_string()),
                Token::new(TokenType::Semicolon, 5, 1, ";".to_string()),
                Token::new(TokenType::Eof, 6, 1, "".to_string()),
            ],
        ];

        for (input, expected_for_input) in inputs.iter().zip(tests) {
            let mut scanner = Scanner::new(input);
            let mut tokens = vec![];

            loop {
                let token = scanner.scan_token();
                let token_type = token.token_type;

                tokens.push(token);
                if token_type == TokenType::Eof {
                    break;
                }
            }

            for (token, expected) in tokens.iter().zip(&expected_for_input) {
                assert_eq!(token, expected);
            }
        }
    }
}
