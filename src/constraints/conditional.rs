use core::fmt;
use std::fmt::Debug;

use crate::{Constraint, ConstraintRepr, Encoder, Lit, SatVar, Solver, VarMap};

use super::util;

/// Implication constraint.
/// If `cond` is satisfied true then the `then` constraint has to be true.
#[derive(Debug, Clone)]
pub struct If<C, T> {
    pub cond: C, // If condition constraint is true
    pub then: T, // then this condition has to be true as well.
}

impl<V, C, T> Constraint<V> for If<C, T>
where
    V: SatVar,
    C: ConstraintRepr<V>,
    T: Constraint<V>,
{
    fn encode<S: Solver>(self, solver: &mut S, varmap: &mut VarMap<V>) {
        let cond_repr = self
            .cond
            .encode_constraint_implies_repr(None, solver, varmap);

        util::repr_implies_constraint(self.then, cond_repr, solver, varmap);
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        constraints::{test_util::retry_until_unsat, AtMostK},
        prelude::*,
    };

    use super::*;

    #[test]
    fn if_then_simple() {
        let mut encoder = Encoder::<_, cadical::Solver>::new();

        let cond = Pos(5);
        let then = Pos(6);

        encoder.add_constraint(If { cond, then });

        let r = retry_until_unsat(&mut encoder, |model| {
            model.print_model();
            if model.var(5).unwrap() {
                assert!(model.var(6).unwrap());
            }
        });
        assert_eq!(r, 3);
    }

    #[test]
    fn if_then_with_constraints() {
        let mut encoder = Encoder::<_, cadical::Solver>::new();

        let cond = AtMostK {
            k: 2,
            lits: (1..=5).map(Pos),
        };
        let then = AtMostK {
            k: 2,
            lits: (3..=7).map(Pos),
        };

        encoder.add_constraint(If { cond, then });

        let r = retry_until_unsat(&mut encoder, |model| {
            model.print_model();
            if (1..=5).filter(|l| model.var(*l).unwrap()).count() <= 2 {
                assert!((3..=7).filter(|l| model.var(*l).unwrap()).count() <= 2)
            }
        });
        assert_eq!(r, 110 /*TODO: Verify this is correct */);
    }
}
