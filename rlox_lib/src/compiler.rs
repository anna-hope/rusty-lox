use std::cell::RefCell;
use std::ops::Add;
use std::rc::Rc;
use std::{env, mem};

use thiserror::Error;
use ustr::Ustr;

use crate::chunk::OpCode::Divide;
use crate::chunk::{Chunk, OpCode, Upvalue};
use crate::scanner::{Scanner, Token, TokenType};
use crate::value::{Function, Obj, ObjClosure, Value};

type BoxedCompiler = Rc<RefCell<Compiler>>;

pub type Result<T> = std::result::Result<T, ParserError>;

type CompilerResult<T> = std::result::Result<T, CompilerError>;

#[derive(Debug, Error)]
pub enum CompilerError {
    #[error("Already a variable with this name in this scope.")]
    SameNameVariableInScope,

    #[error("Can't read local variable in its own initializer.")]
    ReadLocalInInitializer,
}

#[derive(Debug, Error)]
#[error(transparent)]
pub enum ParserError {
    #[error("CompileError")]
    Error,
}

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
            TokenType::RightParen => Precedence::Lowest,
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
            TokenType::And => Precedence::And,
            TokenType::Or => Precedence::Or,
            TokenType::LeftParen => Precedence::Call,
            _ => Precedence::Lowest,
        }
    }
}

#[derive(Debug, Default, Copy, Clone, PartialEq)]
struct Local {
    name: Token,
    depth: usize,
    initialized: bool,
}

impl Local {
    fn new(name: Token, depth: usize) -> Self {
        Self {
            name,
            depth,
            initialized: false,
        }
    }
}

#[derive(Debug, Default, Copy, Clone, PartialEq)]
enum FunctionType {
    Function,
    #[default]
    Script,
}

#[derive(Debug, Clone)]
struct Compiler {
    enclosing: Option<BoxedCompiler>,
    function: Function,
    function_type: FunctionType,
    locals: Vec<Local>,
    upvalues: Vec<Upvalue>,
    scope_depth: usize,
}

impl Compiler {
    fn new(
        enclosing: Option<BoxedCompiler>,
        function_type: FunctionType,
        function_name: Option<Ustr>,
    ) -> Self {
        let mut locals = Vec::with_capacity(u8::MAX.into());
        locals.push(Local::default());

        Self {
            enclosing,
            function: Function::new(function_name),
            function_type,
            locals,
            upvalues: Vec::with_capacity(u8::MAX.into()),
            scope_depth: 0,
        }
    }

    fn add_local(&mut self, name: Token) -> CompilerResult<()> {
        let local = Local::new(name, self.scope_depth);
        if self.locals.contains(&local) {
            return Err(CompilerError::SameNameVariableInScope);
        }

        self.locals.push(local);
        Ok(())
    }

    fn resolve_local(&self, name: Token) -> CompilerResult<Option<usize>> {
        for (index, local) in self.locals.iter().enumerate().rev() {
            if local.name.value == name.value {
                return if local.initialized {
                    Ok(Some(index))
                } else {
                    Err(CompilerError::ReadLocalInInitializer)
                };
            }
        }
        Ok(None)
    }

    fn add_upvalue(&mut self, index: usize, is_local: bool) -> usize {
        for (n, upvalue) in self.upvalues.iter().enumerate() {
            if upvalue.index == index && upvalue.is_local == is_local {
                return n;
            }
        }

        self.upvalues.push(Upvalue { index, is_local });
        self.function.upvalue_count += 1;

        self.upvalues.len() - 1
    }

    fn resolve_upvalue(&mut self, name: Token) -> Option<usize> {
        if let Some(enclosing) = &self.enclosing {
            let maybe_local_index = enclosing.borrow().resolve_local(name).unwrap();
            if let Some(local_index) = maybe_local_index {
                Some(self.add_upvalue(local_index, true))
            } else {
                enclosing
                    .borrow_mut()
                    .resolve_upvalue(name)
                    .map(|upvalue| enclosing.borrow_mut().add_upvalue(upvalue, false))
            }
        } else {
            None
        }
    }

    fn mark_last_local_initialized(&mut self) {
        if self.scope_depth == 0 {
            return;
        }

        self.locals.last_mut().unwrap().initialized = true;
    }

    fn chunk(&self) -> Rc<RefCell<Chunk>> {
        Rc::clone(&self.function.chunk)
    }
}

impl Default for Compiler {
    fn default() -> Self {
        Self::new(None, FunctionType::Script, None)
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Parser {
    scanner: Scanner,
    previous: Option<Token>,
    current: Option<Token>,
    had_error: bool,
    panic_mode: bool,
    compiler: BoxedCompiler,
}

impl Parser {
    pub fn new(source: impl ToString) -> Self {
        let scanner = Scanner::new(source);
        Self {
            scanner,
            previous: None,
            current: None,
            had_error: false,
            panic_mode: false,
            compiler: Rc::new(RefCell::new(Compiler::default())),
        }
    }

    pub fn compile(&mut self) -> Result<Function> {
        self.advance();

        while !self.match_token(TokenType::Eof) {
            self.declaration();
        }

        let function = self.end_compiler();

        if self.had_error {
            Err(ParserError::Error)
        } else {
            Ok(function)
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

    fn error_at_current(&mut self, msg: &str) {
        self.error_at(self.current.as_ref().unwrap(), msg);
        self.panic_mode = true;
        self.had_error = true;
    }

    fn error_at_previous(&mut self, msg: &str) {
        self.error_at(self.previous.as_ref().unwrap(), msg);
        self.panic_mode = true;
        self.had_error = true;
    }

    fn error_at(&self, token: &Token, msg: &str) {
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

        eprintln!(": {}", msg);
    }

    fn consume(&mut self, token_type: TokenType, msg: &str) {
        if self.current.as_ref().unwrap().token_type == token_type {
            self.advance();
        } else {
            self.error_at_current(msg);
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

    fn emit_code(&self, code: OpCode) {
        let previous = self.previous.unwrap();
        let compiler = self.compiler.borrow();
        compiler.chunk().borrow_mut().add_code(code, previous.line);
    }

    fn emit_codes(&self, code1: OpCode, code2: OpCode) {
        self.emit_code(code1);
        self.emit_code(code2);
    }

    fn emit_loop(&self, loop_start: usize) {
        // HACK: Subtracting one from the offset because something funky is going on
        // with instruction pointers on the VM side.
        // Ideally, it would be fixed there, but I haven't been able to figure it out.
        let offset = self.compiler.borrow().chunk().borrow().len() - loop_start + 2 - 1;
        let jump_offset = calculate_jump_offset(offset >> 8 & 0xff, offset & 0xff);
        self.emit_code(OpCode::Loop(jump_offset));
    }

    fn emit_jump(&self, instruction: OpCode) -> usize {
        self.emit_code(instruction);
        let compiler = self.compiler.borrow();
        compiler.chunk().borrow().len() - 1
    }

    fn end_compiler(&mut self) -> Function {
        self.emit_return();

        let function = {
            let compiler = self.compiler.borrow();
            compiler.function.clone()
        };

        if env::var("DEBUG_PRINT_CODE") == Ok("1".to_string()) && !self.had_error {
            let name = function.name.unwrap_or("<script>".into());
            let compiler = self.compiler.borrow();
            compiler.chunk().borrow().disassemble(name.as_str());
        }

        let maybe_enclosing = self.compiler.borrow().enclosing.as_ref().map(Rc::clone);
        if let Some(enclosing) = maybe_enclosing {
            self.compiler = enclosing;
        }

        function
    }

    fn begin_scope(&self) {
        self.compiler.borrow_mut().scope_depth += 1;
    }

    fn end_scope(&self) {
        let num_pops = {
            let mut compiler = self.compiler.borrow_mut();
            compiler.scope_depth -= 1;

            let mut num_pops = 0;

            // Pop all the locals at the current scope.
            while !compiler.locals.is_empty()
                && compiler.locals.last().unwrap().depth > compiler.scope_depth
            {
                num_pops += 1;
                compiler.locals.pop();
            }

            num_pops
        };

        for _ in 0..num_pops {
            self.emit_code(OpCode::Pop);
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

    fn call(&mut self) {
        let arg_count = self.argument_list();
        self.emit_code(OpCode::Call(arg_count));
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

    fn or(&mut self) {
        let else_jump = self.emit_jump(OpCode::JumpIfFalse(0xff));
        let end_jump = self.emit_jump(OpCode::Jump(0xff));

        self.patch_jump(else_jump);
        self.emit_code(OpCode::Pop);

        self.parse_precedence(Precedence::Or);
        self.patch_jump(end_jump);
    }

    fn string(&mut self, _can_assign: bool) {
        let string = self.previous.unwrap().value;
        self.emit_constant(string.into());
    }

    fn named_variable(&mut self, name: Token, can_assign: bool) {
        let maybe_name = { self.compiler.borrow().resolve_local(name) };
        match maybe_name {
            Ok(maybe_arg) => {
                let (get_op, set_op) = if let Some(arg) = maybe_arg {
                    (OpCode::GetLocal(arg), OpCode::SetLocal(arg))
                } else {
                    let maybe_arg = { self.compiler.borrow_mut().resolve_upvalue(name) };
                    if let Some(arg) = maybe_arg {
                        (OpCode::GetUpvalue(arg), OpCode::SetUpvalue(arg))
                    } else {
                        let arg = self.identifier_constant(name);
                        (OpCode::GetGlobal(arg), OpCode::SetGlobal(arg))
                    }
                };

                if can_assign && self.match_token(TokenType::Equal) {
                    self.expression();
                    self.emit_code(set_op);
                } else {
                    self.emit_code(get_op);
                }
            }
            Err(error) => {
                self.error_at_previous(error.to_string().as_str());
            }
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
        match self.previous.unwrap().token_type {
            TokenType::LeftParen => Some(Self::grouping),
            TokenType::Minus => Some(Self::unary),
            TokenType::Number => Some(Self::number),
            TokenType::False | TokenType::True | TokenType::Nil => Some(Self::literal),
            TokenType::Bang => Some(Self::unary),
            TokenType::String => Some(Self::string),
            TokenType::Identifier => Some(Self::variable),
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
            TokenType::And => Some(Self::and),
            TokenType::Or => Some(Self::or),
            TokenType::LeftParen => Some(Self::call),
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

    fn identifier_constant(&self, name: Token) -> usize {
        let compiler = self.compiler.borrow();
        compiler
            .chunk()
            .borrow_mut()
            .push_constant(Value::Obj(Obj::new(name.value)))
    }

    fn declare_variable(&mut self) {
        let result = {
            let mut compiler = self.compiler.borrow_mut();
            if compiler.scope_depth == 0 {
                return;
            }

            let name = self.previous.unwrap();
            compiler.add_local(name)
        };

        if let Err(error) = result {
            self.error_at_previous(error.to_string().as_str());
        }
    }

    fn parse_variable(&mut self, error_msg: &str) -> usize {
        self.consume(TokenType::Identifier, error_msg);

        self.declare_variable();
        if self.compiler.borrow().scope_depth > 0 {
            return 0;
        }

        self.identifier_constant(self.previous.unwrap())
    }

    fn define_variable(&mut self, global_index: usize) {
        {
            let mut compiler = self.compiler.borrow_mut();

            if compiler.scope_depth > 0 {
                compiler.mark_last_local_initialized();
                return;
            }
        }

        self.emit_code(OpCode::DefineGlobal(global_index));
    }

    fn argument_list(&mut self) -> usize {
        let mut arg_count = 0;
        if !self.check(TokenType::RightParen) {
            loop {
                self.expression();

                if arg_count == 255 {
                    self.error_at_previous("Can't have more than 255 arguments.");
                }

                arg_count += 1;
                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }

        self.consume(TokenType::RightParen, "Expect ')' after arguments.");
        arg_count
    }

    fn and(&mut self) {
        let end_jump = self.emit_jump(OpCode::JumpIfFalse(0xff));

        self.emit_code(OpCode::Pop);
        self.parse_precedence(Precedence::And);

        self.patch_jump(end_jump);
    }

    fn expression(&mut self) {
        self.parse_precedence(Precedence::Assignment);
    }

    fn block(&mut self) {
        while !self.check(TokenType::RightBrace) && !self.check(TokenType::Eof) {
            self.declaration();
        }

        self.consume(TokenType::RightBrace, "Expect '}' after block.");
    }

    fn function(&mut self, function_type: FunctionType) {
        let function_name = self.previous.unwrap().value;
        let compiler = Rc::new(RefCell::new(Compiler::new(
            Some(Rc::clone(&self.compiler)),
            function_type,
            Some(function_name),
        )));
        self.compiler = Rc::clone(&compiler);
        self.begin_scope();

        self.consume(TokenType::LeftParen, "Expect '(' after function name.");
        if !self.check(TokenType::RightParen) {
            loop {
                {
                    let boxed_compiler = Rc::clone(&self.compiler);
                    let mut compiler = boxed_compiler.borrow_mut();
                    compiler.function.arity += 1;
                    if compiler.function.arity > 255 {
                        self.error_at_current("Can't have more than 255 parameters.");
                    }
                }

                let constant = self.parse_variable("Expect parameter name");
                self.define_variable(constant);

                if !self.match_token(TokenType::Comma) {
                    break;
                }
            }
        }

        self.consume(TokenType::RightParen, "Expect ')' after parameters.");
        self.consume(TokenType::LeftBrace, "Expect '{' before function body.");
        self.block();

        let function = self.end_compiler();
        let upvalues = &compiler.borrow().upvalues;

        self.emit_closure(
            Value::Closure(Rc::new(RefCell::new(ObjClosure::new(function)))),
            upvalues,
        );
    }

    fn fun_declaration(&mut self) {
        let global = self.parse_variable("Expect function name.");
        self.compiler.borrow_mut().mark_last_local_initialized();
        self.function(FunctionType::Function);
        self.define_variable(global);
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

    fn for_statement(&mut self) {
        self.begin_scope();
        self.consume(TokenType::LeftParen, "Expect '(' after 'for'.");
        if self.match_token(TokenType::Semicolon) {
            // No initializer.
        } else if self.match_token(TokenType::Var) {
            self.var_declaration();
        } else {
            self.expression_statement();
        }

        let mut loop_start = {
            let compiler = self.compiler.borrow();
            compiler.chunk().borrow().len()
        };

        let mut exit_jump: Option<usize> = None;
        if !self.match_token(TokenType::Semicolon) {
            self.expression();
            self.consume(TokenType::Semicolon, "Expect ';' after loop condition.");

            // Jump out of the loop if the condition is false.
            exit_jump = Some(self.emit_jump(OpCode::JumpIfFalse(0xff)));
            self.emit_code(OpCode::Pop); // Condition
        }

        if !self.match_token(TokenType::RightParen) {
            let body_jump = self.emit_jump(OpCode::Jump(0xff));
            let increment_start = { self.compiler.borrow().chunk().borrow().len() };
            self.expression();
            self.emit_code(OpCode::Pop);
            self.consume(TokenType::RightParen, "Expect ')' after for clauses.");

            self.emit_loop(loop_start);
            loop_start = increment_start;
            self.patch_jump(body_jump);
        }

        self.statement();
        self.emit_loop(loop_start);

        if let Some(exit_jump) = exit_jump {
            self.patch_jump(exit_jump);
            self.emit_code(OpCode::Pop); // Condition.
        }

        self.end_scope();
    }

    fn if_statement(&mut self) {
        self.consume(TokenType::LeftParen, "Expect '(' after 'if'.");
        self.expression();
        self.consume(TokenType::RightParen, "Expect ')' after condition.");

        let then_jump = self.emit_jump(OpCode::JumpIfFalse(0xff));
        self.emit_code(OpCode::Pop);
        self.statement();

        let else_jump = self.emit_jump(OpCode::Jump(0xff));

        self.patch_jump(then_jump);
        self.emit_code(OpCode::Pop);

        if self.match_token(TokenType::Else) {
            self.statement();
        }

        self.patch_jump(else_jump);
    }

    fn print_statement(&mut self) {
        self.expression();
        self.consume(TokenType::Semicolon, "Expect ';' after value.");
        self.emit_code(OpCode::Print);
    }

    fn return_statement(&mut self) {
        if matches!(self.compiler.borrow().function_type, FunctionType::Script) {
            self.error_at_previous("Can't return from top-level code.");
        }

        if self.match_token(TokenType::Semicolon) {
            self.emit_return();
        } else {
            self.expression();
            self.consume(TokenType::Semicolon, "Expect ';' after return value.");
            self.emit_code(OpCode::Return);
        }
    }

    fn while_statement(&mut self) {
        let loop_start = { self.compiler.borrow().chunk().borrow().len() };
        self.consume(TokenType::LeftParen, "Expect '(' after 'while'.");
        self.expression();
        self.consume(TokenType::RightParen, "Expect ')' after condition.");

        let exit_jump = self.emit_jump(OpCode::JumpIfFalse(0xff));
        self.emit_code(OpCode::Pop);
        self.statement();
        self.emit_loop(loop_start);

        self.patch_jump(exit_jump);
        self.emit_code(OpCode::Pop);
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
        if self.match_token(TokenType::Fun) {
            self.fun_declaration();
        } else if self.match_token(TokenType::Var) {
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
        } else if self.match_token(TokenType::For) {
            self.for_statement();
        } else if self.match_token(TokenType::If) {
            self.if_statement();
        } else if self.match_token(TokenType::Return) {
            self.return_statement();
        } else if self.match_token(TokenType::While) {
            self.while_statement();
        } else if self.match_token(TokenType::LeftBrace) {
            self.begin_scope();
            self.block();
            self.end_scope();
        } else {
            self.expression_statement();
        }
    }

    fn emit_return(&self) {
        // Return nil if the function doesn't return anything.
        self.emit_code(OpCode::Nil);
        self.emit_code(OpCode::Return);
    }

    fn emit_constant(&self, value: Value) {
        let previous = self.previous.unwrap();
        let compiler = self.compiler.borrow();
        compiler
            .chunk()
            .borrow_mut()
            .add_constant_code(value, previous.line);
    }

    fn emit_closure(&self, value: Value, upvalues: &[Upvalue]) {
        let previous = self.previous.unwrap();
        let compiler = self.compiler.borrow();
        compiler
            .chunk()
            .borrow_mut()
            .add_closure(value, previous.line, upvalues);
    }

    fn patch_jump(&self, offset: usize) {
        let compiler = self.compiler.borrow();
        // HACK: Ditto about subtracting 1 from the offset.
        let jump = compiler.chunk().borrow().len() - offset - 1;

        match compiler.chunk().borrow_mut().codes.get_mut(offset).unwrap() {
            OpCode::JumpIfFalse(ref mut offset) | OpCode::Jump(ref mut offset) => {
                *offset = calculate_jump_offset(jump >> 8 & 0xff, jump & 0xff);
            }
            _ => panic!("Expected Jump or JumpIfFalse"),
        }
    }
}

#[inline]
fn calculate_jump_offset(offset1: usize, offset2: usize) -> usize {
    // Combining two 8-bit offsets from the book into one offset here for better VM ergonomics.
    // We don't have to store them as two separate u8's because we use usize.
    offset1 << 8 | offset2
}
