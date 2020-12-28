use core::fmt;
use std::fmt::Debug;

use crate::{Constraint, Encoder, Lit, SatVar, VarMap};

/// Implication constraint.
/// If all of `cond` are true then the `then` constraint has to be true.
#[derive(Clone)]
pub struct If<I1, C> {
    pub cond: I1, // if all lits of cond iterator are true
    pub then: C,  // then this condition has to be true as well.
}

struct IfThenEncoderWrapper<'a, E> {
    internal: &'a mut E,
    prefix: Vec<i32>,
}

impl<'a, V: SatVar, E: Encoder<V>> Encoder<V> for IfThenEncoderWrapper<'a, E> {
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

impl<V: SatVar + Debug, I, C> Debug for If<I, C>
where
    I: Iterator<Item = Lit<V>> + Clone,
    C: Constraint<V>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<_> = self.cond.clone().collect();

        f.debug_tuple("If").field(&lits).field(&self.then).finish()
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    use super::*;

    //#[test]
    //fn if_then() {
    //    let mut solver = Solver::new();

    //    let cond = Pos(5);
    //    let then = Pos(6);

    //    solver.add_constraint(If { cond, then });

    //    let r = retry_until_unsat(&mut solver, ||);
    //    assert_eq!(r, 1 + )
    //}
}
