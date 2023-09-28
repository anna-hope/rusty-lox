use std::fmt;

use ustr::Ustr;

use crate::chunk::Chunk;

#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Obj {
    pub name: Option<Ustr>,
}

impl Obj {
    pub fn new(name: Ustr) -> Self {
        Self { name: Some(name) }
    }
}

impl fmt::Display for Obj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = if let Some(name) = self.name {
            name
        } else {
            "UNNAMED".into()
        };
        write!(f, "{name}")
    }
}

#[derive(Debug, Default, Clone, PartialEq)]
pub struct Function {
    pub obj: Obj,
    pub arity: usize,
    pub chunk: Chunk,
    pub name: Option<Ustr>,
}

impl Function {
    pub fn new(name: Option<Ustr>) -> Self {
        Self {
            obj: Obj::default(),
            arity: 0,
            name,
            chunk: Chunk::new(),
        }
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let string = if let Some(name) = self.name {
            name.to_string()
        } else {
            "<script>".to_string()
        };
        write!(f, "{string}")
    }
}

pub type NativeFn = fn(arg_count: usize, args: &mut [Value]) -> Value;

#[derive(Debug, Clone, PartialEq)]
pub struct ObjNative {
    pub obj: Obj,
    pub function: NativeFn,
}

impl ObjNative {
    pub fn new(function: NativeFn) -> Self {
        Self {
            obj: Obj::default(),
            function,
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq)]
pub enum Value {
    Bool(bool),
    #[default]
    Nil,
    Number(f64),
    String(Ustr),
    Obj(Obj),
    Function(Function),
    ObjNative(ObjNative),
}

impl Value {
    pub fn is_number(&self) -> bool {
        matches!(self, Self::Number(_))
    }

    pub fn is_falsey(&self) -> bool {
        match self {
            Self::Nil => true,
            Self::Bool(value) => !value,
            _ => false,
        }
    }

    pub fn is_string(&self) -> bool {
        matches!(self, Self::String(_))
    }

    pub fn name(&self) -> Option<Ustr> {
        match self {
            Self::Obj(obj) => obj.name,
            Self::Function(function) => function.name,
            _ => None,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let string = match self {
            Self::Number(value) => value.to_string(),
            Self::Bool(value) => value.to_string(),
            Self::Nil => "nil".to_string(),
            Self::String(string) => string.to_owned(),
            Self::Obj(value) => value.to_string(),
            Self::Function(function) => function.to_string(),
            Self::ObjNative(_) => "<native fn>".to_string(),
        };
        write!(f, "{string}")
    }
}

impl From<f64> for Value {
    fn from(value: f64) -> Self {
        Self::Number(value)
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Self::Bool(value)
    }
}

impl From<String> for Value {
    fn from(value: String) -> Self {
        Self::String(Ustr::from(value.as_str()))
    }
}

impl From<Ustr> for Value {
    fn from(value: Ustr) -> Self {
        Self::String(value)
    }
}

impl From<Function> for Value {
    fn from(value: Function) -> Self {
        Self::Function(value)
    }
}
