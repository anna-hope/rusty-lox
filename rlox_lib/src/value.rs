use fnv::FnvHashMap;
use std::cell::RefCell;
use std::fmt;
use std::fmt::Formatter;
use std::rc::Rc;

use ustr::Ustr;

use crate::chunk::Chunk;

pub(crate) type BoxedValue = Rc<Value>;
pub(crate) type BoxedObjClosure = Rc<RefCell<ObjClosure>>;
pub(crate) type BoxedChunk = Rc<RefCell<Chunk>>;
pub(crate) type BoxedObjClass = Rc<RefCell<ObjClass>>;
pub(crate) type BoxedObjInstance = Rc<RefCell<ObjInstance>>;
pub(crate) type BoxedObjBoundMethod = Rc<RefCell<ObjBoundMethod>>;

#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub(crate) struct Obj {
    pub name: Option<Ustr>,
}

impl Obj {
    pub fn new(name: Ustr) -> Self {
        Self { name: Some(name) }
    }
}

impl fmt::Display for Obj {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = self.name.unwrap_or("UNNAMED".into());
        write!(f, "{name}")
    }
}

#[derive(Debug, Default, Clone, PartialEq)]
pub(crate) struct Function {
    pub obj: Obj,
    pub arity: usize,
    pub chunk: BoxedChunk,
    pub name: Option<Ustr>,
    pub upvalue_count: usize,
}

impl Function {
    pub fn new(name: Option<Ustr>) -> Self {
        Self {
            obj: Obj::default(),
            arity: 0,
            name,
            chunk: Rc::new(RefCell::new(Chunk::new())),
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

#[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ObjClass {
    pub obj: Obj,
    pub name: Ustr,
    pub methods: FnvHashMap<Ustr, BoxedObjClosure>,
}

impl ObjClass {
    pub fn new(name: Ustr) -> Self {
        Self {
            obj: Obj::default(),
            name,
            methods: FnvHashMap::default(),
        }
    }
}

impl fmt::Display for ObjClass {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ObjInstance {
    pub obj: Obj,
    pub class: BoxedObjClass,
    pub fields: FnvHashMap<Ustr, BoxedValue>,
}

impl ObjInstance {
    pub fn new(class: BoxedObjClass) -> Self {
        Self {
            obj: Obj::default(),
            class,
            fields: FnvHashMap::default(),
        }
    }
}

impl fmt::Display for ObjInstance {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} instance", self.class.borrow().name)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ObjBoundMethod {
    pub obj: Obj,
    pub receiver: BoxedValue,
    pub method: BoxedObjClosure,
}

impl fmt::Display for ObjBoundMethod {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.method.borrow().function)
    }
}

impl ObjBoundMethod {
    pub fn new(receiver: BoxedValue, method: BoxedObjClosure) -> Self {
        Self {
            obj: Obj::default(),
            receiver,
            method,
        }
    }
}

pub(crate) type BoxedObjUpvalue = Rc<RefCell<ObjUpvalue>>;

#[derive(Debug, Clone, PartialEq)]
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
            closed: Rc::new(Value::Nil),
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq)]
pub(crate) enum Value {
    Bool(bool),
    #[default]
    Nil,
    Number(f64),
    String(Ustr),
    Obj(Obj),
    ObjNative(ObjNative),
    Closure(BoxedObjClosure),
    Class(BoxedObjClass),
    Instance(BoxedObjInstance),
    BoundMethod(BoxedObjBoundMethod),
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
            Self::Class(class) => class.borrow().to_string(),
            Self::Instance(instance) => instance.borrow().to_string(),
            Self::BoundMethod(method) => method.borrow().to_string(),
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
