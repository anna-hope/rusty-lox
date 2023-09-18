#[derive(Default, Debug, Clone, PartialEq)]
pub enum Value {
    Bool(bool),
    #[default]
    Nil,
    Number(f64),
}

impl Value {
    pub fn is_number(&self) -> bool {
        match self {
            Self::Number(_) => true,
            _ => false,
        }
    }

    pub fn is_falsey(&self) -> bool {
        match self {
            Self::Nil => true,
            Self::Bool(value) => !value,
            _ => false,
        }
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
