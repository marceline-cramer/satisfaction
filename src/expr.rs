use std::{fmt::Debug, hash::Hash, str::FromStr, sync::Arc};

use im::HashSet;

pub type Clause<T> = Arc<[Literal<T>]>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Literal<T> {
    pub variable: T,
    pub polarity: bool,
}

impl FromStr for Literal<String> {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(rest) = s.strip_prefix('!') {
            Ok(Literal {
                variable: rest.to_string(),
                polarity: false,
            })
        } else {
            Ok(Literal {
                variable: s.to_string(),
                polarity: true,
            })
        }
    }
}

impl<T> Literal<T> {
    pub fn negate(self) -> Self {
        Self {
            variable: self.variable,
            polarity: !self.polarity,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BoolExpr<T: Clone + Ord + Hash> {
    Variable(T),
    Not(Arc<Self>),
    And(HashSet<Self>),
    Or(HashSet<Self>),
    Xor(Box<Self>, Box<Self>),
    Iff(Box<Self>, Box<Self>),
}

impl<T: Clone + Ord + Hash> From<T> for BoolExpr<T> {
    fn from(var: T) -> Self {
        Self::Variable(var)
    }
}

impl<T: Clone + Ord + Hash> From<Literal<T>> for BoolExpr<T> {
    fn from(lit: Literal<T>) -> Self {
        let var = Self::from(lit.variable);
        if lit.polarity {
            var
        } else {
            var.not()
        }
    }
}

impl<T: Clone + Ord + Hash> BoolExpr<T> {
    pub fn not(&self) -> Self {
        if let Self::Not(not) = self {
            not.as_ref().to_owned()
        } else {
            Self::Not(Arc::new(self.clone()))
        }
    }

    pub fn iff(&self, other: &Self) -> Self {
        Self::Iff(Box::new(self.clone()), Box::new(other.clone()))
    }

    pub fn xor(&self, other: &Self) -> Self {
        Self::Xor(Box::new(self.clone()), Box::new(other.clone()))
    }

    pub fn and(&self, other: &Self) -> Self {
        Self::And(FromIterator::from_iter([self.clone(), other.clone()]))
    }

    pub fn or(&self, other: &Self) -> Self {
        Self::Or(FromIterator::from_iter([self.clone(), other.clone()]))
    }
}
