use std::fmt;
use std::fmt::Formatter;

use gc::{unsafe_empty_trace, Finalize, Gc, GcCell, Trace};
use ustr::Ustr;

use crate::chunk::Chunk;

pub(crate) type BoxedValue = Gc<Value>;

#[derive(Debug, Default, Clone, Copy, PartialEq, Finalize)]
pub(crate) struct Obj {
    pub name: Option<Ustr>,
}

impl Obj {
    pub fn new(name: Ustr) -> Self {
        Self { name: Some(name) }
    }
}

unsafe impl Trace for Obj {
    unsafe_empty_trace!();
}

impl fmt::Display for Obj {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = if let Some(name) = self.name {
            name
        } else {
            "UNNAMED".into()
        };
        write!(f, "{name}")
    }
}

#[derive(Debug, Clone, PartialEq, Trace, Finalize)]
pub(crate) struct Function {
    pub obj: Obj,
    pub arity: usize,
    pub chunk: Gc<GcCell<Chunk>>,
    #[unsafe_ignore_trace]
    pub name: Option<Ustr>,
    pub upvalue_count: usize,
}

impl Default for Function {
    fn default() -> Self {
        Self {
            obj: Default::default(),
            arity: Default::default(),
            chunk: Gc::new(GcCell::new(Default::default())),
            name: Default::default(),
            upvalue_count: Default::default(),
        }
    }
}

impl Function {
    pub fn new(name: Option<Ustr>) -> Self {
        Self {
            obj: Obj::default(),
            arity: 0,
            name,
            chunk: Gc::new(GcCell::new(Chunk::new())),
            upvalue_count: 0,
        }
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let string = if let Some(name) = self.name {
            name.to_string()
        } else {
            "<script>".to_string()
        };
        write!(f, "{string}")
    }
}

pub(crate) type NativeFnResult = Result<Option<Value>, Box<dyn std::error::Error>>;

pub(crate) type NativeFn = fn(args: &mut [BoxedValue]) -> NativeFnResult;

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ObjNative {
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

#[derive(Debug, Clone, PartialEq, Trace, Finalize)]
pub(crate) struct ObjClosure {
    pub obj: Obj,
    pub function: Function,
    pub upvalues: Vec<BoxedObjUpvalue>,
}

impl ObjClosure {
    pub fn new(function: Function) -> Self {
        let upvalue_count = function.upvalue_count;
        Self {
            obj: Obj::default(),
            function,
            upvalues: Vec::with_capacity(upvalue_count),
        }
    }
}

impl fmt::Display for ObjClosure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.function)
    }
}

pub(crate) type BoxedObjUpvalue = Gc<GcCell<ObjUpvalue>>;

#[derive(Debug, Clone, PartialEq, Trace, Finalize)]
pub(crate) struct ObjUpvalue {
    pub obj: Obj,
    pub location: BoxedValue,
    pub next: Option<BoxedObjUpvalue>,
    pub closed: BoxedValue,
}

impl ObjUpvalue {
    pub fn new(slot: BoxedValue) -> Self {
        Self {
            obj: Obj::default(),
            location: slot,
            next: None,
            closed: Gc::new(Value::Nil),
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq, Trace, Finalize)]
pub(crate) enum Value {
    Bool(bool),
    #[default]
    Nil,
    Number(f64),
    String(#[unsafe_ignore_trace] Ustr),
    Obj(Obj),
    ObjNative(#[unsafe_ignore_trace] ObjNative),
    Closure(Gc<GcCell<ObjClosure>>),
}

impl Value {
    pub fn is_falsey(&self) -> bool {
        match self {
            Self::Nil => true,
            Self::Bool(value) => !value,
            _ => false,
        }
    }

    pub fn name(&self) -> Option<Ustr> {
        match self {
            Self::Obj(obj) => obj.name,
            Self::Closure(closure) => closure.borrow().function.name,
            _ => None,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let string = match self {
            Self::Number(value) => value.to_string(),
            Self::Bool(value) => value.to_string(),
            Self::Nil => "nil".to_string(),
            Self::String(string) => string.to_owned(),
            Self::Obj(value) => value.to_string(),
            Self::ObjNative(_) => "<native fn>".to_string(),
            Self::Closure(closure) => closure.borrow().to_string(),
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
