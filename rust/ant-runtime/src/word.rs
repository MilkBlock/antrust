use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Word {
    Int(i32),
    ConstructorTag(i32),
}

impl Word {
    pub fn value(&self) -> i32 {
        match self {
            Word::Int(value) | Word::ConstructorTag(value) => *value,
        }
    }

    pub fn raw_repr(&self) -> (i32, i32) {
        match self {
            Word::Int(value) => (0, *value),
            Word::ConstructorTag(value) => (1, *value),
        }
    }
}

impl fmt::Display for Word {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Word::Int(value) => write!(f, "I({})", value),
            Word::ConstructorTag(value) => write!(f, "C({})", value),
        }
    }
}
