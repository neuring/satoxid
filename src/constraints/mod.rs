use core::fmt;
use std::{
    fmt::Debug,
    iter::once,
    ops::{BitAnd, BitOr, Neg},
};

use super::{Constraint, Encoder, Lit, SatVar, VarMap};

mod expr;
mod cardinality;

pub use expr::Expr;
pub use cardinality::{AtMostK, AtleastK};

#[macro_export]
macro_rules! clause {
    ($($e:expr),*) => {
        [$($e),*].iter().copied()
    }
}

impl<V: SatVar + Debug> Constraint<V> for Lit<V> {
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let var = solver.varmap().add_var(self);
        solver.add_clause(clause!(var));
    }
}

/// Constraint which represents a simple clause.
#[derive(Clone)]
pub struct Clause<I>(pub I);

impl<V: SatVar, I: Clone> Constraint<V> for Clause<I>
where
    V: Debug + Clone,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let clause: Vec<_> = self.0.map(|lit| solver.varmap().add_var(lit)).collect();
        solver.add_clause(clause.into_iter());
    }
}

impl<I, V> Debug for Clause<I>
where
    V: Debug,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.0.clone()).finish()
    }
}

/// Implication constraint.
/// If all of `cond` are true then the `then` constraint has to be true.
pub struct If<I1, C> {
    pub cond: I1, // if all lits of cond iterator are true
    pub then: C,  // then this condition has to be true as well.
}

struct IfThenEncoderWrapper<'a, E> {
    internal: &'a mut E,
    prefix: Vec<i32>,
}

impl<'a, V, E: Encoder<V>> Encoder<V> for IfThenEncoderWrapper<'a, E> {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>,
    {
        self.internal
            .add_clause(lits.chain(self.prefix.iter().copied()));
    }

    fn varmap(&mut self) -> &mut VarMap<V> {
        self.internal.varmap()
    }
}

impl<V, C, I1> Constraint<V> for If<I1, C>
where
    V: Debug + Clone + SatVar,
    C: Constraint<V>,
    I1: Iterator<Item = Lit<V>> + Clone,
{
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let prefix = self.cond.map(|lit| solver.varmap().add_var(-lit)).collect();

        let mut solver = IfThenEncoderWrapper {
            internal: solver,
            prefix,
        };

        self.then.encode(&mut solver);
    }
}

impl<V: Debug, I, C> Debug for If<I, C>
where
    I: Iterator<Item = Lit<V>> + Clone,
    C: Constraint<V>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<_> = self.cond.clone().collect();

        f.debug_tuple("If").field(&lits).field(&self.then).finish()
    }
}
