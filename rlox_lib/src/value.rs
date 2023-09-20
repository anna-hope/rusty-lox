use std::fmt;

use ustr::Ustr;

#[derive(Default, Debug, Clone, PartialEq)]
pub enum Value {
    Bool(bool),
    #[default]
    Nil,
    Number(f64),
    String(Ustr),
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
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let string = match self {
            Self::Number(value) => value.to_string(),
            Self::Bool(value) => value.to_string(),
            Self::Nil => "nil".to_string(),
            Self::String(string) => string.to_owned(),
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
