use std::{fmt::Debug, hash::Hash, str::FromStr, sync::Arc};

use im::{HashSet, OrdSet};

pub type Clause<T> = Arc<[Literal<T>]>;

/// Tests if a clause is tautological.
pub fn clause_is_tautological<T: Clone + Ord>(clause: &[Literal<T>]) -> bool {
    for lit in clause.iter() {
        if lit.polarity && clause.contains(&lit.clone().negate()) {
            return true;
        }
    }

    false
}

/// Negates a clause.
///
/// Note that through De Morgan's law, this requires that the clause swaps
/// between conjunctive and disjunctive connectives.
pub fn negate_clause<T: Clone + Ord>(clause: &Clause<T>) -> Clause<T> {
    clause.iter().cloned().map(Literal::negate).collect()
}

/// Converts a set of DNF clauses into CNF clauses.
pub fn dnf_to_cnf<T: Clone + Ord>(clauses: &OrdSet<Clause<T>>) -> OrdSet<Clause<T>> {
    // handle the empty case
    if clauses.is_empty() {
        return OrdSet::new();
    }

    // start with a single, empty clause to find the product with
    let mut product = vec![Vec::new()];

    // find a new product using each clause in the set
    for clause in clauses.iter() {
        let mut new_product = Vec::with_capacity(product.len() * clause.len());

        for old_clause in product {
            for lit in clause.iter() {
                // avoid constructing tautological clauses
                if old_clause.contains(&lit.clone().negate()) {
                    continue;
                }

                // create a new clause
                let mut new_clause = old_clause.clone();
                new_clause.push(lit.clone());
                new_product.push(new_clause);
            }
        }

        product = new_product;
    }

    // return the total product
    product.into_iter().map(Clause::from).collect()
}

/// Finds a CNF-form of the disjunction of a list of CNF clauses.
pub fn cnf_conjunction<T: Clone + Ord>(
    terms: impl IntoIterator<Item = OrdSet<Clause<T>>>,
) -> OrdSet<Clause<T>> {
    // start with a single, empty clause to find the product with
    let mut product = vec![Vec::new()];

    // find a new product from each term in the list
    for term in terms.into_iter() {
        let mut new_product = Vec::with_capacity(product.len() * term.len());

        for old_clause in product {
            for clause in term.iter() {
                // create a new clause
                let mut new_clause = old_clause.clone();
                new_clause.extend(clause.iter().cloned());

                // push the new product while avoiding tautologies
                if !clause_is_tautological(&new_clause) {
                    new_product.push(new_clause);
                }
            }
        }

        product = new_product;
    }

    // return the total product
    product.into_iter().map(Clause::from).collect()
}

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

impl<T: Clone + Debug + Ord + Hash> BoolExpr<T> {
    pub fn into_cnf(&self) -> OrdSet<Clause<T>> {
        let start = std::time::Instant::now();
        use BoolExpr::*;
        let cnf = match self {
            // initialize a unit clause from a single variable
            Variable(variable) => OrdSet::unit(Arc::from_iter([Literal {
                variable: variable.clone(),
                polarity: true,
            }])),
            // AND of CNF terms is just merging them
            And(terms) => terms.iter().flat_map(Self::into_cnf).collect(),
            // XOR by explicitly expressing cases and finding CNF
            Xor(lhs, rhs) => lhs.and(&rhs.not()).or(&lhs.not().and(rhs)).into_cnf(),
            // if-and-only-if by explicitly expressing and finding CNF
            Iff(lhs, rhs) => lhs.and(rhs).or(&lhs.not().and(&rhs.not())).into_cnf(),
            // negate each clause of the subterm then convert back from DNF to CNF
            Not(term) => dnf_to_cnf(&term.into_cnf().iter().map(negate_clause).collect()),
            // Or(x, y, ...) <=> Not(And(Not(x), Not(y), ...))
            Or(terms) => {
                // since we're finding Not() twice, we don't negate the literals in clauses
                let terms = terms
                    .iter()
                    .map(|term| term.into_cnf())
                    .flat_map(|term| dnf_to_cnf(&term))
                    .collect();

                dnf_to_cnf(&terms)
            }
        };

        eprintln!("found CNF of {self:?} in {:?}", start.elapsed());

        cnf
    }

    pub fn not(&self) -> Self {
        if let Self::Not(not) = self {
            not.as_ref().to_owned()
        } else {
            Self::Not(Arc::new(self.clone()))
        }
    }

    pub fn and(&self, other: &Self) -> Self {
        Self::And(FromIterator::from_iter([self.clone(), other.clone()]))
    }

    pub fn or(&self, other: &Self) -> Self {
        Self::Or(FromIterator::from_iter([self.clone(), other.clone()]))
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    macro_rules! var {
        ($var:expr) => {
            BoolExpr::from(stringify!($var).to_string())
        };
    }

    macro_rules! literal {
        (($var:expr)) => {
            Literal::from_str(stringify!($var)).unwrap()
        };
    }

    macro_rules! clause {
    ($($term:expr),+) => {
        Clause::from_iter([$(literal!(($term))),*])
    }
}

    #[test]
    fn cnf_identity() {
        let a = var!(a);
        let expected = OrdSet::from_iter([clause!(a)]);
        assert_eq!(a.into_cnf(), expected);
    }

    #[test]
    fn cnf_negated_identity() {
        let a = var!(a);
        let expected = OrdSet::from_iter([clause!(!a)]);
        assert_eq!(a.not().into_cnf(), expected);
    }

    #[test]
    fn cnf_basic_and() {
        let a = var!(a);
        let b = var!(b);
        let expected = OrdSet::from_iter([clause!(a), clause!(b)]);
        assert_eq!(a.and(&b).into_cnf(), expected);
    }

    #[test]
    fn cnf_basic_or() {
        let a = var!(a);
        let b = var!(b);
        let expected = OrdSet::from_iter([clause!(a, b)]);
        assert_eq!(a.or(&b).into_cnf(), expected);
    }

    #[test]
    fn cnf_basic_de_morgans_or() {
        let a = var!(a);
        let b = var!(b);
        let expected = OrdSet::from_iter([clause!(!a), clause!(!b)]);
        assert_eq!(a.or(&b).not().into_cnf(), expected);
    }

    #[test]
    fn cnf_basic_de_morgans_and() {
        let a = var!(a);
        let b = var!(b);
        let expected = OrdSet::from_iter([clause!(!a, !b)]);
        assert_eq!(a.and(&b).not().into_cnf(), expected);
    }
}
