use core::fmt;
use std::{
    fmt::Debug,
    iter::once,
    ops::{BitAnd, BitOr},
};

use super::{Constraint, Encoder, Lit, SatVar, VarMap};
use crate::{ConstraintRepr, Solver, VarType};

mod cardinality;
mod conditional;
mod expr;
pub(crate) mod util;

#[cfg(test)]
mod test_util;

pub use cardinality::{AtMostK, AtleastK, ExactlyK, SameCardinality};
pub use conditional::If;
pub use expr::Expr;

#[doc(hidden)]
#[macro_export]
macro_rules! clause {
    ($($e:expr),*) => {
        [$($e),*].iter().copied()
    }
}

impl<V: SatVar> Constraint<V> for Lit<V> {
    fn encode<S: Solver>(self, solver: &mut S, varmap: &mut VarMap<V>) {
        let var = varmap.add_var(self);
        solver.add_clause(clause!(var));
    }
}

impl<V: SatVar> ConstraintRepr<V> for Lit<V> {
    fn encode_constraint_implies_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| varmap.new_var());
        let var = varmap.add_var(self);

        solver.add_clause(clause![-var, repr]);

        repr
    }

    fn encode_constraint_equals_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {

        let var = varmap.add_var(self);

        if let Some(repr) = repr {
            solver.add_clause(clause![-var, repr]);
            solver.add_clause(clause![var, -repr]);
            repr
        } else {
            var
        }
    }
}

impl<V: SatVar> Constraint<V> for VarType<V> {
    fn encode<S: Solver>(self, solver: &mut S, varmap: &mut VarMap<V>) {
        let var = varmap.add_var(self);
        solver.add_clause(clause!(var));
    }
}

impl<V: SatVar> ConstraintRepr<V> for VarType<V> {
    fn encode_constraint_implies_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| varmap.new_var());
        let var = varmap.add_var(self);

        solver.add_clause(clause![-var, repr]);

        repr
    }

    fn encode_constraint_equals_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {

        let var = varmap.add_var(self);

        if let Some(repr) = repr {
            solver.add_clause(clause![-var, repr]);
            solver.add_clause(clause![var, -repr]);
            repr
        } else {
            var
        }
    }
}

/// Constraint which represents a simple clause.
#[derive(Clone)]
pub struct Or<I>(pub I);

impl<I, L, V> Constraint<V> for Or<I>
where
    V: SatVar,
    L: Into<VarType<V>> + Debug,
    I: Iterator<Item = L> + Clone,
{
    fn encode<S: Solver>(self, solver: &mut S, varmap: &mut VarMap<V>) {
        solver.add_clause(self.0.map(|lit| varmap.add_var(lit.into())));
    }
}

impl<I, L, V> ConstraintRepr<V> for Or<I>
where
    V: SatVar,
    L: Into<VarType<V>> + Debug,
    I: Iterator<Item = L> + Clone,
{
    fn encode_constraint_implies_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| varmap.new_var());

        for lit in self.0 {
            let sat_lit = varmap.add_var(lit);

            solver.add_clause(clause![-sat_lit, repr]);
        }

        repr
    }
}

impl<I, V> Debug for Or<I>
where
    V: Debug,
    I: Iterator<Item = V> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list: Vec<_> = self.0.clone().collect();
        f.debug_tuple("Or").field(&list).finish()
    }
}

/// Constraint which requires all lits to be true.
/// In some ways it's the opposite of `Clause`.
#[derive(Clone)]
pub struct And<I>(pub I);

impl<V, L, I> Constraint<V> for And<I>
where
    V: SatVar,
    L: Into<VarType<V>> + Debug,
    I: Iterator<Item = L> + Clone,
{
    fn encode<S: Solver>(self, solver: &mut S, varmap: &mut VarMap<V>) {
        for v in self.0 {
            let v = varmap.add_var(v);
            solver.add_clause(clause![v]);
        }
    }
}

impl<V, L, I> ConstraintRepr<V> for And<I>
where
    V: SatVar,
    L: Into<VarType<V>> + Debug,
    I: Iterator<Item = L> + Clone,
{
    fn encode_constraint_implies_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| varmap.new_var());

        let vars = self.0.map(|l| -varmap.add_var(l));
        solver.add_clause(vars.chain(clause![repr]));

        repr
    }
}

impl<I, V> Debug for And<I>
where
    V: Debug,
    I: Iterator<Item = V> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list: Vec<_> = self.0.clone().collect();
        f.debug_tuple("And").field(&list).finish()
    }
}

/// Constraint which requires all lits to be same value.
#[derive(Clone)]
pub struct Equal<I>(pub I);

impl<V, L, I> Constraint<V> for Equal<I>
where
    V: SatVar,
    L: Into<VarType<V>> + Debug,
    I: Iterator<Item = L> + Clone,
{
    fn encode<S: Solver>(self, solver: &mut S, varmap: &mut VarMap<V>) {
        let lits: Vec<_> = self.0.map(|l| varmap.add_var(l)).collect();

        for l in lits.windows(2) {
            solver.add_clause(clause![-l[0], l[1]]);
        }

        solver.add_clause(clause![-lits[lits.len() - 1], lits[0]]);
    }
}

impl<V, L, I> ConstraintRepr<V> for Equal<I>
where
    V: SatVar,
    L: Into<VarType<V>> + Debug,
    I: Iterator<Item = L> + Clone,
{
    fn encode_constraint_implies_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| varmap.new_var());
        let lits: Vec<_> = self.0.clone().map(|l| varmap.add_var(l)).collect();

        solver.add_clause(lits.iter().copied().chain(clause![repr]));
        solver.add_clause(lits.into_iter().map(|l| -l).chain(clause![repr]));

        repr
    }
}

impl<I, V> Debug for Equal<I>
where
    V: Debug,
    I: Iterator<Item = V> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list: Vec<_> = self.0.clone().collect();
        f.debug_tuple("Equal").field(&list).finish()
    }
}

#[derive(Debug, Clone)]
pub struct Not<C>(pub C);

impl<V, C> Constraint<V> for Not<C> 
where V: SatVar,
      C: ConstraintRepr<V>,
{
    fn encode<S: Solver>(self, solver: &mut S, varmap: &mut VarMap<V>) {
        let repr = self.0.encode_constraint_implies_repr(None, solver, varmap);

        solver.add_clause(clause![-repr]);
    }
}

impl<V, C> ConstraintRepr<V> for Not<C> 
where V: SatVar,
      C: ConstraintRepr<V>,
{
    fn encode_constraint_implies_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let not_repr = repr.unwrap_or_else(|| varmap.new_var());
        let repr = self.0.encode_constraint_equals_repr(None, solver, varmap);

        solver.add_clause(clause![repr, not_repr]);

        not_repr
    }

    fn encode_constraint_equals_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let not_repr = repr.unwrap_or_else(|| varmap.new_var());
        let repr = self.0.encode_constraint_equals_repr(None, solver, varmap);

        solver.add_clause(clause![repr, not_repr]);
        solver.add_clause(clause![-repr, -not_repr]);

        not_repr
    }
}

#[cfg(test)]
mod tests {
    use super::{
        test_util::{
            constraint_equals_repr_tester, constraint_implies_repr_tester,
            retry_until_unsat,
        },
        *,
    };
    use crate::{ConstraintRepr, DefaultEncoder, Encoder, Lit, Solver, VarType};

    use num_integer::binomial;

    #[test]
    fn lit_implies_repr() {
        let mut encoder = DefaultEncoder::new();

        let lit = Lit::Pos(1);

        let repr = encoder.varmap.new_var();
        let r = lit.encode_constraint_implies_repr(
            Some(repr),
            &mut encoder.solver,
            &mut encoder.varmap,
        );
        assert_eq!(repr, r);

        let res = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            model.lit(lit).unwrap()
        });
        assert_eq!(res.correct, 1);
        assert_eq!(res.total(), 2);
    }

    #[test]
    fn lit_implies_repr_none() {
        let mut encoder = DefaultEncoder::new();

        let lit = Lit::Pos(1);

        let repr = lit.encode_constraint_implies_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );

        let res = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            model.lit(lit).unwrap()
        });
        assert_eq!(res.correct, 1);
        assert_eq!(res.total(), 2);
    }

    #[test]
    fn lit_equals_repr() {
        let mut encoder = DefaultEncoder::new();

        let lit = Lit::Pos(1);

        let repr = encoder.varmap.new_var();
        let r = lit.encode_constraint_equals_repr(
            Some(repr),
            &mut encoder.solver,
            &mut encoder.varmap,
        );
        assert_eq!(repr, r);

        let res = constraint_equals_repr_tester(&mut encoder, r, |model| {
            model.lit(lit).unwrap()
        });
        assert_eq!(res.correct, 1);
        assert_eq!(res.total(), 2);
    }

    #[test]
    fn clause_implies_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 6;
        let clause = Or((1..=range).map(Lit::Pos));

        let r = clause.encode_constraint_implies_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );

        let res = constraint_implies_repr_tester(&mut encoder, r, |model| {
            model.vars().filter(|l| matches!(l, Lit::Pos(_))).count() > 0
        });
        assert_eq!(res.correct, (1 << range) - 1);
        assert_eq!(res.total(), (1 << range));
    }

    #[test]
    fn clause_equals_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 6;
        let clause = Or((1..=range).map(Lit::Pos));

        let r = clause.encode_constraint_equals_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );

        let res = constraint_equals_repr_tester(&mut encoder, r, |model| {
            model.vars().filter(|l| matches!(l, Lit::Pos(_))).count() > 0
        });
        assert_eq!(res.correct, (1 << range) - 1);
        assert_eq!(res.total(), (1 << range));
    }

    #[test]
    fn and_implies_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 6;
        let constraint = And((1..=range).map(Lit::Pos));

        let r = constraint.encode_constraint_implies_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );
        dbg!(r);

        let res = constraint_implies_repr_tester(&mut encoder, r, |model| {
            model.vars().filter(|l| matches!(l, Lit::Pos(_))).count() == range
        });
        assert_eq!(res.correct, 1);
        assert_eq!(res.total(), (1 << range));
    }

    #[test]
    fn and_equals_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 6;
        let constraint = And((1..=range).map(Lit::Pos));

        let r = constraint.encode_constraint_equals_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );

        let res = constraint_equals_repr_tester(&mut encoder, r, |model| {
            model.vars().filter(|l| matches!(l, Lit::Pos(_))).count() == range
        });
        assert_eq!(res.correct, 1);
        assert_eq!(res.total(), (1 << range));
    }

    #[test]
    fn equal_constraint() {
        let mut encoder = DefaultEncoder::new();

        let range = 7;
        let constraint = Equal((1..=range).map(Lit::Pos));

        encoder.add_constraint(constraint);

        let res = retry_until_unsat(&mut encoder, |model| {
            assert!(
                model.vars().all(|l| matches!(l, Lit::Pos(_)))
                    || model.vars().all(|l| matches!(l, Lit::Neg(_)))
            );
        });
        assert_eq!(res, 2);
    }

    #[test]
    fn equal_implies_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 6;
        let constraint = Equal((1..=range).map(Lit::Pos));

        let r = constraint.encode_constraint_implies_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );
        dbg!(r);

        let res = constraint_implies_repr_tester(&mut encoder, r, |model| {
            model.vars().all(|l| matches!(l, Lit::Pos(_)))
                || model.vars().all(|l| matches!(l, Lit::Neg(_)))
        });
        assert_eq!(res.correct, 2);
        assert_eq!(res.total(), (1 << range));
    }

    #[test]
    fn equal_equals_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 6;
        let constraint = Equal((1..=range).map(Lit::Pos));

        let r = constraint.encode_constraint_equals_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );

        let res = constraint_equals_repr_tester(&mut encoder, r, |model| {
            model.vars().all(|l| matches!(l, Lit::Pos(_)))
                || model.vars().all(|l| matches!(l, Lit::Neg(_)))
        });
        assert_eq!(res.correct, 2);
        assert_eq!(res.total(), (1 << range));
    }

    #[test]
    fn not_constraint() {
        let mut encoder = DefaultEncoder::new();

        let range = 6;
        let k = 3;
        let constraint = AtleastK { k, lits: (0..range).map(Lit::Pos)};

        let constraint = Not(constraint);

        encoder.add_constraint(constraint);

        let res = retry_until_unsat(&mut encoder, |model| {
            assert!(
                model.vars().filter(|l| matches!(l, Lit::Pos(_))).count() < k as usize
            );
        });
        assert_eq!(res as u32, (0..k).map(|i| binomial(range, i)).sum());
    }

    #[test]
    fn not_implies_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 6;
        let k = 3;
        let constraint = AtleastK { k, lits: (0..range).map(Lit::Pos)};

        let constraint = Not(constraint);

        let repr = constraint.encode_constraint_implies_repr(None, &mut encoder.solver, &mut encoder.varmap);

        let res = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            model.vars().filter(|l| matches!(l, Lit::Pos(_))).count() < k as usize
        });
        assert_eq!(res.correct as u32, (0..k).map(|i| binomial(range, i)).sum());
        assert_eq!(res.total() as u32, 1 << range);
    }

    #[test]
    fn not_equals_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 6;
        let k = 3;
        let constraint = AtleastK { k, lits: (0..range).map(Lit::Pos)};

        let constraint = Not(constraint);

        let repr = constraint.encode_constraint_equals_repr(None, &mut encoder.solver, &mut encoder.varmap);

        let res = constraint_equals_repr_tester(&mut encoder, repr, |model| {
            model.vars().filter(|l| matches!(l, Lit::Pos(_))).count() < k as usize
        });
        assert_eq!(res.correct as u32, (0..k).map(|i| binomial(range, i)).sum());
        assert_eq!(res.total() as u32, 1 << range);
    }
}
