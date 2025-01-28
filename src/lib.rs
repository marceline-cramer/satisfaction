use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    sync::{Arc, Mutex},
};

use expr::{BoolExpr, Clause, Literal};
use im::OrdSet;

pub mod expr;

/// Parses a DIMACS file from a string. Panics on syntax errors.
pub fn read_dimacs(src: &str) -> OrdSet<Clause<i32>> {
    let mut words = src
        .lines()
        .filter(|line| !line.starts_with('c'))
        .flat_map(|line| line.split_whitespace());

    assert_eq!(words.next(), Some("p"));
    assert_eq!(words.next(), Some("cnf"));

    let _var_num: usize = words
        .next()
        .expect("expected variable count")
        .parse()
        .expect("failed to parse variable count");

    let _clause_num: usize = words
        .next()
        .expect("expected clause count")
        .parse()
        .expect("failed to parse clause count");

    let mut clauses = OrdSet::new();
    let mut clause = Vec::new();

    for word in words {
        if let Some(word) = word.strip_prefix('-') {
            let variable = word.parse().expect("failed to parse variable");
            let polarity = false;
            let lit = Literal { variable, polarity };
            clause.push(lit);
        } else if word == "%" {
            break;
        } else if word == "0" {
            let clause = std::mem::take(&mut clause);
            clauses.insert(clause.into());
        } else {
            let variable = word.parse().expect("failed to parse variable");
            let polarity = true;
            let lit = Literal { variable, polarity };
            clause.push(lit);
        }
    }

    clauses
}

/// A trait for incremental SAT solver backends.
pub trait Backend {
    /// Adds a clause to the SAT problem.
    fn add_clause(&mut self, vars: &[i32]);

    /// Checks the satisfiability of the current SAT problem.
    fn check(&mut self, assumptions: &[i32]) -> SatResult;

    /// Retrieves the value of the given literal.
    fn value(&self, lit: i32) -> bool;
}

#[cfg(feature = "cadical")]
pub mod cadical {
    use cadical::{Callbacks, Solver};

    use super::{Backend, SatResult};

    pub struct CadicalBackend<C: Callbacks> {
        solver: Solver<C>,
    }

    impl<C: Callbacks> Default for CadicalBackend<C> {
        fn default() -> Self {
            Self {
                solver: Solver::new(),
            }
        }
    }

    impl<C: Callbacks> Backend for CadicalBackend<C> {
        fn add_clause(&mut self, vars: &[i32]) {
            self.solver.add_clause(vars.iter().copied());
        }

        fn check(&mut self, assumptions: &[i32]) -> SatResult {
            use SatResult::*;
            let result = match self.solver.solve_with(assumptions.iter().copied()) {
                Some(true) => Sat,
                Some(false) => Unsat,
                None => Unknown,
            };

            result
        }

        fn value(&self, lit: i32) -> bool {
            self.solver.value(lit).unwrap()
        }
    }
}

pub struct Scope<T, B> {
    solver: Arc<Mutex<Solver<T, B>>>,
    staging: HashSet<i32>,
    parent_vars: HashSet<i32>,
    parent: Option<Arc<Self>>,
}

impl<T: Clone + Debug + Ord + Hash, B: Backend> Scope<T, B> {
    pub fn new(solver: Solver<T, B>) -> Self {
        Self {
            solver: Arc::new(Mutex::new(solver)),
            staging: HashSet::new(),
            parent_vars: HashSet::new(),
            parent: None,
        }
    }

    pub fn push(&mut self) -> Self {
        // only create a new shared parent if we have new unstaged clauses
        if !self.staging.is_empty() || self.parent.is_none() {
            // migrate our variables into a new parent
            self.parent = Some(Arc::new(Self {
                solver: self.solver.clone(),
                staging: self.staging.clone(),
                parent_vars: self.parent_vars.clone(),
                parent: self.parent.clone(),
            }));

            // update our parent vars
            self.parent_vars.extend(self.staging.drain());
        }

        // now clone our unstaged state
        Self {
            solver: self.solver.clone(),
            staging: self.staging.clone(),
            parent_vars: self.parent_vars.clone(),
            parent: self.parent.clone(),
        }
    }

    pub fn assert(&mut self, expr: BoolExpr<T>) -> &mut Self {
        // lock the solver
        let mut solver = self.solver.lock().unwrap();

        // do the Tseitin transformation to get the relevant clauses
        let (gate, clauses) = solver.tseitin_cnf(&expr);

        // if we have no parent, we immediately commit this clause without gating it
        if self.parent.is_none() {
            solver.backend.add_clause(&[gate]);
        } else {
            // otherwise, we're staging this gate for assumptions
            self.staging.insert(gate);
        }

        // add each of the clauses in CNF form
        for clause in clauses {
            solver.backend.add_clause(&clause);
        }

        // return self reference to chain multiple assertions
        drop(solver);
        self
    }

    pub fn check(&self) -> SatResult {
        let mut solver = self.solver.lock().unwrap();
        let mut assumptions = Vec::from_iter(self.parent_vars.iter().copied());
        assumptions.extend(self.staging.iter().copied());
        solver.check(&assumptions)
    }
}

pub struct Solver<T, B> {
    backend: B,
    next_var: i32,
    variables: HashMap<T, i32>,
    uncommitted: HashSet<i32>,
    last_result: SatResult,
}

impl<T: Clone + Ord + Hash, B: Backend> Solver<T, B> {
    /// Creates a new solver with the given backend.
    pub fn new(backend: B) -> Self {
        Self {
            backend,
            next_var: 1,
            variables: HashMap::new(),
            uncommitted: HashSet::new(),
            last_result: SatResult::Unknown,
        }
    }

    /// Gets a reference to the backend in use.
    pub fn get_backend(&self) -> &B {
        &self.backend
    }

    /// Gets a mutable reference to the backend in use.
    pub fn get_backend_mut(&mut self) -> &mut B {
        &mut self.backend
    }

    /// Gets the value of a variable, if it exists and the problem has been successfully checked.
    pub fn get_value(&self, var: T) -> Option<bool> {
        if self.last_result != SatResult::Sat {
            return None;
        }

        let var = self.variables.get(&var)?;

        Some(self.backend.value(*var))
    }

    /// Gets an identifier for an unused variable.
    pub fn unique_variable(&mut self) -> i32 {
        let var = self.next_var;
        self.next_var += 1;
        var
    }

    /// Gets the identifier for a variable. Assigns one if one exists.
    pub fn load_variable(&mut self, var: T) -> i32 {
        use std::collections::hash_map::Entry;
        match self.variables.entry(var) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let var = self.next_var;
                entry.insert(var);
                self.next_var += 1;
                var
            }
        }
    }

    /// Gets a temporary variable.
    pub fn temp_var(&mut self) -> i32 {
        let this = &mut *self;
        let var = this.next_var;
        this.next_var += 1;
        self.uncommitted.insert(var);
        var
    }

    /// Commit a temporary variable to either being unused or used.
    pub fn commit(&mut self, lit: i32) {
        if self.uncommitted.remove(&lit.abs()) {
            self.backend.add_clause(&[lit]);
        }
    }

    /// Adds a clause directly to the problem.
    pub fn add_clause(&mut self, clause: Clause<T>) {
        let vars = self.map_clause(clause);
        self.backend.add_clause(&vars);
    }

    /// Performs the Tseitin transformation on a Boolean expression.
    ///
    /// Returns transformed clauses and the output variable for the whole expression.
    pub fn tseitin_cnf(&mut self, expr: &BoolExpr<T>) -> (i32, Vec<Vec<i32>>) {
        use BoolExpr::*;
        match expr {
            Variable(var) => (self.load_variable(var.clone()), vec![]),
            Not(term) => {
                let (input, mut clauses) = self.tseitin_cnf(term);
                let output = self.unique_variable();
                clauses.push(vec![input, output]);
                clauses.push(vec![-input, -output]);
                (output, clauses)
            }
            And(terms) => {
                let output = self.unique_variable();
                let mut all_case = vec![output];
                let mut clauses = Vec::new();

                for term in terms.iter() {
                    let (input, new_clauses) = self.tseitin_cnf(term);
                    clauses.extend(new_clauses);
                    all_case.push(-input);
                    clauses.push(vec![input, -output])
                }

                clauses.push(all_case);

                (output, clauses)
            }
            Or(terms) => {
                let output = self.unique_variable();
                let mut none_case = vec![-output];
                let mut clauses = Vec::new();

                for term in terms.iter() {
                    let (input, new_clauses) = self.tseitin_cnf(term);
                    clauses.extend(new_clauses);
                    none_case.push(input);
                    clauses.push(vec![-input, output])
                }

                clauses.push(none_case);

                (output, clauses)
            }
            Xor(lhs, rhs) => {
                let mut clauses = Vec::new();
                let (lhs, new_clauses) = self.tseitin_cnf(lhs);
                clauses.extend(new_clauses);
                let (rhs, new_clauses) = self.tseitin_cnf(rhs);
                clauses.extend(new_clauses);
                let output = self.unique_variable();
                clauses.push(vec![-lhs, -rhs, -output]);
                clauses.push(vec![lhs, rhs, -output]);
                clauses.push(vec![-lhs, rhs, output]);
                clauses.push(vec![lhs, -rhs, output]);
                (output, clauses)
            }
            Iff(lhs, rhs) => {
                let mut clauses = Vec::new();
                let (lhs, new_clauses) = self.tseitin_cnf(lhs);
                clauses.extend(new_clauses);
                let (rhs, new_clauses) = self.tseitin_cnf(rhs);
                clauses.extend(new_clauses);
                let output = self.unique_variable();
                clauses.push(vec![-lhs, -rhs, output]);
                clauses.push(vec![lhs, rhs, output]);
                clauses.push(vec![-lhs, rhs, -output]);
                clauses.push(vec![lhs, -rhs, -output]);
                (output, clauses)
            }
        }
    }

    /// Helper to map a clause to a list of variable indices.
    fn map_clause(&mut self, clause: Clause<T>) -> Vec<i32> {
        clause
            .iter()
            .cloned()
            .map(|lit| {
                let var = self.load_variable(lit.variable);

                if lit.polarity {
                    var
                } else {
                    -var
                }
            })
            .collect()
    }

    /// Checks the satisfiability of the existing SAT problem under the given assumptions.
    pub fn check(&mut self, assumptions: &[i32]) -> SatResult {
        self.last_result = self.backend.check(assumptions);
        self.last_result
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SatResult {
    Sat,
    Unsat,
    Unknown,
}
