#![allow(unused)]

use core::fmt;
use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    marker::PhantomData,
    ops::{Add, BitAnd, BitOr, Neg},
};

mod constraints;

pub mod prelude {
    pub use super::{constraints::Clause, Encoder, Lit::{self, *}, Solver};
}

pub use constraints::{AtMostK, AtleastK, If, Expr};

/// Generic interface for solvers (or Wrapper) to implement.
pub trait Encoder<V>: Sized {
    /// Add raw clause as integer SAT variable.
    /// These are usually determined using `VarMap`.
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>;

    /// Return the used `VarMap` of the solver.
    fn varmap(&mut self) -> &mut VarMap<V>;

    /// Add a constraint.
    fn add_constraint<C: Constraint<V>>(&mut self, constraint: C) {
        constraint.encode(self);
    }
}

/// Trait used to express a constraint.
/// Constraints represent define a finite set of clauses.
pub trait Constraint<V>: Debug {
    /// Encode `Self` as an constraint using `solver`.
    fn encode<E: Encoder<V>>(self, solver: &mut E);
}

/// Enum to describe the polarity of variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum Lit<V> {
    Pos(V),
    Neg(V),
}

impl<V> Lit<V> {
    /// Returns the underlying variable.
    #[allow(unused)]
    pub fn var(&self) -> &V {
        match self {
            Lit::Pos(v) | Lit::Neg(v) => v,
        }
    }
}

impl<V> Neg for Lit<V> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Lit::Pos(v) => Lit::Neg(v),
            Lit::Neg(v) => Lit::Pos(v),
        }
    }
}

/// Trait which expresses the required trait bounds for a variable.
pub trait SatVar: Hash + Eq + Clone {}

impl<V: Hash + Eq + Clone> SatVar for V {}

/// Mapper from user defined variables and integer sat variables used by the
/// solver backend.
pub struct VarMap<V> {
    forward: HashMap<V, i32>,
    reverse: HashMap<i32, V>,
    next_id: i32,
}

impl<V> Default for VarMap<V> {
    fn default() -> Self {
        Self {
            forward: Default::default(),
            reverse: Default::default(),
            next_id: 1,
        }
    }
}

impl<V: Debug> Debug for VarMap<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map: Vec<_> = self.forward.iter().collect();
        map.sort_by_key(|&(_, &i)| i);

        f.debug_list().entries(map).finish()
    }
}

impl<V: SatVar> VarMap<V> {

    /// Translates an element of type `V` to a integer SAT variable used by the 
    /// backend solver.
    /// If `var` wasn't already used it generates a new SAT variable.
    /// Depending on whether `var` is `Pos` or `Neg` the returned value is 
    /// positive or negative.
    pub fn add_var(&mut self, lit: Lit<V>) -> i32 {
        let (var, pol) = match lit {
            Lit::Pos(v) => (v, 1),
            Lit::Neg(v) => (v, -1),
        };

        let id = if let Some(id) = self.forward.get(&var) {
            *id
        } else {
            let id = self.new_var();

            self.forward.insert(var.clone(), id);
            self.reverse.insert(id, var);

            id
        };

        pol * id
    }

    /// Same as `add_var` but it won't insert new `Lit<V>` instead returning `None`.
    pub fn get_var(&self, lit: Lit<V>) -> Option<i32> {
        let (var, pol) = match lit {
            Lit::Pos(v) => (v, 1),
            Lit::Neg(v) => (v, -1),
        };

        Some(pol * self.forward.get(&var).copied()?)
    }


    /// Lookup the correct `V` based on the integer SAT variable.
    pub fn lookup(&self, lit: i32) -> Option<&V> {
        self.reverse.get(&lit)
    }

    /// Returns the number of used variables.
    /// NOTE: This might be larger than the used SATVars.
    pub fn num_vars(&self) -> usize {
        self.next_id as usize
    }
}

impl<V> VarMap<V> {
    /// Generates fresh (unused) SAT variable.
    pub fn new_var(&mut self) -> i32 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }
}

/// Default Solver implementation using the cadical sat solver.
pub struct Solver<V> {
    pub internal: cadical::Solver,
    varmap: VarMap<V>,
}

impl<V: SatVar> Solver<V> {

    /// Creates a new solver.
    pub fn new() -> Self {
        Self {
            internal: cadical::Solver::new(),
            varmap: VarMap::default(),
        }
    }

    /// Solve the encoded problem.
    /// If problem is unsat then `None` is returned.
    /// Otherwise the set of all used `Lit<V>` is returned `Pos` or `Neg` depending
    /// on what is required for the model to satisfy.
    pub fn solve(&mut self) -> Option<HashSet<Lit<V>>> {
        let result = self.internal.solve();

        if let Some(true) = result {
            let result = (1..=self.varmap.num_vars())
                .filter_map(|v| {
                    let sat_var = self.varmap.lookup(v as i32)?.clone();

                    if self.internal.value(v as i32).unwrap_or(true) {
                        Some(Lit::Pos(sat_var))
                    } else {
                        Some(Lit::Neg(sat_var))
                    }
                })
                .collect();
            Some(result)
        } else {
            None
        }
    }
}

impl<V> Encoder<V> for Solver<V> {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>,
    {
        self.internal.add_clause(lits);
    }

    fn varmap(&mut self) -> &mut VarMap<V> {
        &mut self.varmap
    }
}

/// Helper Encoder implementation which prints out the added constraints to stdout.
/// It has the same API as `Solver` but will panic if `solve` is called because
/// it doesn't encode anything.
/// Its purpose is to allow for easy insight on what constraints are getting encoded.
#[derive(Debug)]
pub struct DebugSolver<V>(VarMap<V>);

impl<V> DebugSolver<V> {
    /// Creates new instance of `DebugSolver`.
    pub fn new() -> Self {
        Self(Default::default())
    }

    /// Function for API parity with `Solver`.
    /// #Panics
    /// Always
    pub fn solve(&mut self) -> Option<HashSet<Lit<V>>> {
        panic!("Cannot solve a DebugSolver");
    }
}

impl<V> Encoder<V> for DebugSolver<V> {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>,
    {
    }

    fn varmap(&mut self) -> &mut VarMap<V> {
        &mut self.0
    }

    fn add_constraint<C: Constraint<V>>(&mut self, constraint: C) {
        dbg!(constraint);
    }
}
