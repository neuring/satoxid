use std::fmt::Debug;

use super::util;
use crate::{
    clause, Constraint, ConstraintRepr, SatVar, Backend, VarMap,
};

/// Implication constraint.
/// If `cond` is satisfied true then the `then` constraint has to be true.
#[derive(Debug, Clone)]
pub struct If<C, T> {
    pub cond: C, // If condition constraint is true
    pub then: T, // then this constraint has to be true as well.
}

impl<V, C, T> Constraint<V> for If<C, T>
where
    V: SatVar,
    C: ConstraintRepr<V>,
    T: Constraint<V>,
{
    fn encode<B: Backend>(self, backend: &mut B, varmap: &mut VarMap<V>) {
        let cond_repr = self
            .cond
            .encode_constraint_repr_cheap(None, backend, varmap);

        util::repr_implies_constraint(self.then, cond_repr, backend, varmap);
    }
}

impl<V, C, T> ConstraintRepr<V> for If<C, T>
where
    V: SatVar,
    C: ConstraintRepr<V>,
    T: ConstraintRepr<V>,
{
    fn encode_constraint_implies_repr<B: Backend>(
        self,
        repr: Option<i32>,
        backend: &mut B,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| varmap.new_var());

        let cond_repr = self
            .cond
            .encode_constraint_equals_repr(None, backend, varmap);
        let then_repr = self
            .then
            .encode_constraint_equals_repr(None, backend, varmap);

        backend.add_clause(clause![cond_repr, repr]);
        backend.add_clause(clause![-cond_repr, -then_repr, repr]);

        repr
    }

    fn encode_constraint_equals_repr<B: Backend>(
        self,
        repr: Option<i32>,
        backend: &mut B,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| varmap.new_var());

        let cond_repr = self
            .cond
            .encode_constraint_equals_repr(None, backend, varmap);
        let then_repr = self
            .then
            .encode_constraint_equals_repr(None, backend, varmap);

        backend.add_clause(clause![cond_repr, repr]);
        backend.add_clause(clause![-cond_repr, -then_repr, repr]);

        backend.add_clause(clause![then_repr, -cond_repr, -repr]);

        repr
    }
}

#[cfg(test)]
mod tests {
    use num_integer::binomial;

    use super::*;
    use crate::{
        constraints::{
            test_util::{
                constraint_equals_repr_tester, constraint_implies_repr_tester,
                retry_until_unsat,
            },
            AtMostK,
        },
        CadicalEncoder,
        Lit::*,
    };

    #[test]
    fn if_then_simple() {
        let mut encoder = CadicalEncoder::<u32>::new();

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
        let mut encoder = CadicalEncoder::<u32>::new();

        let cond = AtMostK {
            k: 2,
            lits: 1..=5,
        };
        let then = AtMostK {
            k: 2,
            lits: 3..=7,
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

    #[test]
    fn if_then_implies_repr() {
        let mut encoder = CadicalEncoder::<u32>::new();

        let range = 5;
        let k = 3;
        let cond = AtMostK {
            k,
            lits: 0..range,
        };
        let then = range;
        let constraint = If { cond, then };

        let repr = constraint.encode_constraint_implies_repr(
            None,
            &mut encoder.backend,
            &mut encoder.varmap,
        );

        let r = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            let cond = model
                .vars()
                .filter(|l| (0..range).contains(&l.unwrap()))
                .filter(|l| l.is_pos())
                .count()
                <= k as usize;
            let then = model.var(range).unwrap();

            !cond || then
        });
        assert_eq!(
            r.correct as u32,
            (0..=k).map(|i| binomial(range, i)).sum::<u32>()
                + 2 * ((k + 1)..=range).map(|i| binomial(range, i)).sum::<u32>()
        );
        assert_eq!(r.total(), 1 << (range + 1));
    }

    #[test]
    fn if_then_equals_repr() {
        let mut encoder = CadicalEncoder::<u32>::new();

        let range = 5;
        let k = 3;
        let cond = AtMostK {
            k,
            lits: 0..range,
        };
        let then = Pos(range);
        let constraint = If { cond, then };

        let repr = constraint.encode_constraint_equals_repr(
            None,
            &mut encoder.backend,
            &mut encoder.varmap,
        );

        let r = constraint_equals_repr_tester(&mut encoder, repr, |model| {
            let cond = model
                .vars()
                .filter(|l| (0..range).contains(&l.unwrap()))
                .filter(|l| l.is_pos())
                .count()
                <= k as usize;
            let then = model.var(range).unwrap();

            !cond || then
        });
        assert_eq!(
            r.correct as u32,
            (0..=k).map(|i| binomial(range, i)).sum::<u32>()
                + 2 * ((k + 1)..=range).map(|i| binomial(range, i)).sum::<u32>()
        );
        assert_eq!(r.total(), 1 << (range + 1));
    }
}
