use core::fmt;
use std::{
    fmt::Debug,
    iter::once,
    ops::{BitAnd, BitOr, Neg},
};

use crate::ConstraintRepr;

use super::{Constraint, Encoder, Lit, SatVar, VarMap};

mod cardinality;
mod conditional;
mod expr;
pub(crate) mod util;

#[cfg(test)]
mod test_util;

pub use cardinality::{AtMostK, AtleastK};
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
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let var = solver.varmap().add_var(self);
        solver.add_clause(clause!(var));
    }
}

impl<V: SatVar> ConstraintRepr<V> for Lit<V> {
    fn encode_constraint_implies_repr<E: Encoder<V>>(
        self,
        repr: Option<i32>,
        solver: &mut E,
    ) -> i32 {
        let var = solver.varmap().add_var(self);

        if let Some(repr) = repr {
            solver.add_clause(clause![-var, repr]);
            repr
        } else {
            var
        }
    }
}

/// Constraint which represents a simple clause.
#[derive(Clone)]
pub struct Clause<I>(pub I);

impl<V, I> Constraint<V> for Clause<I>
where
    V: SatVar,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let clause: Vec<_> = self.0.map(|lit| solver.varmap().add_var(lit)).collect();
        solver.add_clause(clause.into_iter());
    }
}

impl<V, I> ConstraintRepr<V> for Clause<I>
where
    V: SatVar,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode_constraint_implies_repr<E: Encoder<V>>(
        self,
        repr: Option<i32>,
        solver: &mut E,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| solver.varmap().new_var());

        for lit in self.0 {
            let sat_lit = solver.varmap().add_var(lit);

            solver.add_clause(clause![-sat_lit, repr]);
        }

        repr
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

/// Constraint which requires all lits to be true.
/// In some ways it's the opposite of `Clause`.
#[derive(Clone)]
pub struct And<I>(I);

impl<V, I> Constraint<V> for And<I>
where
    V: SatVar,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        for v in self.0 {
            let v = solver.varmap().add_var(v);
            solver.add_clause(clause![v]);
        }
    }
}

impl<V, I> ConstraintRepr<V> for And<I>
where
    V: SatVar,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode_constraint_implies_repr<E: Encoder<V>>(
        self,
        repr: Option<i32>,
        solver: &mut E,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| solver.varmap().new_var());

        let vars: Vec<_> = self.0.map(|l| solver.varmap().add_var(l)).collect();
        solver.add_clause(vars.iter().copied().chain(clause![-repr]));

        repr
    }
}

impl<I, V> Debug for And<I>
where
    V: Debug,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list: Vec<_> = self.0.clone().collect();
        f.debug_tuple("And").field(&list).finish()
    }
}

#[cfg(test)]
mod tests {
    use crate::{ConstraintRepr, Encoder, Lit, Solver, VarType};

    use super::{test_util::retry_until_unsat, *};

    #[test]
    fn lit_implies_repr() {
        let mut solver = Solver::new();

        let lit = Lit::Pos(1);

        let repr = solver.varmap().new_var();
        let r = lit.encode_constraint_implies_repr(Some(repr), &mut solver);
        assert_eq!(repr, r);

        let res = retry_until_unsat(&mut solver, |model| {
            model.print_model();
            if model.lit(lit).unwrap() {
                assert!(model.lit_internal(VarType::Unnamed(repr)))
            }
        });
        assert_eq!(res, 2);
    }

    #[test]
    fn lit_equals_repr() {
        let mut solver = Solver::new();

        let lit = Lit::Pos(1);

        let repr = solver.varmap().new_var();
        let r = lit.encode_constraint_equals_repr(Some(repr), &mut solver);
        assert_eq!(repr, r);

        let res = retry_until_unsat(&mut solver, |model| {
            model.print_model();
            if model.lit(lit).unwrap() {
                assert!(model.lit_internal(VarType::Unnamed(repr)))
            } else {
                assert!(model.lit_internal(VarType::Unnamed(-repr)))
            }
        });
        assert_eq!(res, 2);
    }

    #[test]
    fn clause_implies_repr() {
        let mut solver = Solver::new();

        let clause = Clause((1..=6).map(Lit::Pos));

        let r = clause.encode_constraint_implies_repr(None, &mut solver);

        let res = retry_until_unsat(&mut solver, |model| {
            model.print_model();

            if model.vars().filter(|l| matches!(l, Lit::Pos(_))).count() > 0 {
                assert!(model.lit_internal(VarType::Unnamed(r)))
            }
        });
        assert_eq!(res, 64);
    }

    #[test]
    fn clause_equals_repr() {
        let mut solver = Solver::new();

        let clause = Clause((1..=6).map(Lit::Pos));

        let r = clause.encode_constraint_equals_repr(None, &mut solver);

        let res = retry_until_unsat(&mut solver, |model| {
            model.print_model();

            if model.vars().filter(|l| matches!(l, Lit::Pos(_))).count() > 0 {
                assert!(model.lit_internal(VarType::Unnamed(r)))
            } else {
                assert!(model.lit_internal(VarType::Unnamed(-r)))
            }
        });
        assert_eq!(res, 64);
    }

    #[test]
    fn and_implies_repr() {
        let mut solver = Solver::new();

        let constraint = And((1..=6).map(Lit::Pos));

        let r = constraint.encode_constraint_implies_repr(None, &mut solver);

        let res = retry_until_unsat(&mut solver, |model| {
            model.print_model();

            if model.vars().filter(|l| matches!(l, Lit::Pos(_))).count() == 6 {
                assert!(model.lit_internal(VarType::Unnamed(r)))
            }
        });
        assert_eq!(res, 64);
    }

    #[test]
    fn and_equals_repr() {
        let mut solver = Solver::new();

        let constraint = And((1..=6).map(Lit::Pos));

        let r = constraint.encode_constraint_equals_repr(None, &mut solver);

        let res = retry_until_unsat(&mut solver, |model| {
            model.print_model();

            if model.vars().filter(|l| matches!(l, Lit::Pos(_))).count() == 6 {
                assert!(model.lit_internal(VarType::Unnamed(r)))
            } else {
                assert!(model.lit_internal(VarType::Unnamed(-r)))
            }
        });
        assert_eq!(res, 64);
    }
}
