use std::{
    fmt::{self, Debug},
    iter::once,
    ops::{BitAnd, BitOr, Not},
};

use crate::{clause, Constraint, ConstraintRepr, Encoder, Lit, SatVar, VarMap};

use super::util::ClauseCollector;

/// Tseitin Encoding of propositional logic formulas.
#[derive(Clone)]
pub enum Expr<V> {
    And(Box<Expr<V>>, Box<Expr<V>>),
    Or(Box<Expr<V>>, Box<Expr<V>>),
    Not(Box<Expr<V>>),
    Lit(Lit<V>),
    Constraint(ExprConstraint<V>),
}

impl<V: Debug> Debug for Expr<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::And(lhs, rhs) => f.debug_tuple("And").field(&lhs).field(&rhs).finish(),
            Expr::Or(lhs, rhs) => f.debug_tuple("Or").field(&lhs).field(&rhs).finish(),
            Expr::Not(e) => f.debug_tuple("Neg").field(&e).finish(),
            Expr::Lit(lit) => f.debug_tuple("Lit").field(&lit).finish(),
            Expr::Constraint(constraint) => {
                f.debug_tuple("Constraint").field(&constraint.0).finish()
            }
        }
    }
}

pub struct ExprConstraint<V>(Box<dyn DynConstraint<V>>);

impl<V> Clone for ExprConstraint<V> {
    fn clone(&self) -> Self {
        Self(self.0.dyn_clone())
    }
}

impl<V: SatVar> Debug for ExprConstraint<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<V: SatVar> ExprConstraint<V> {
    fn new<C>(constraint: C) -> Self
    where
        C: ConstraintRepr<V> + Clone + 'static,
    {
        Self(Box::new(constraint))
    }
}

impl<V: SatVar> Expr<V> {
    pub fn from_constraint<C>(constraint: C) -> Self
    where
        C: ConstraintRepr<V> + 'static,
    {
        Self::Constraint(ExprConstraint::new(constraint))
    }
}

trait DynConstraint<V>: Debug {
    fn encode_repr(self: Box<Self>, solver: &mut ClauseCollector<V>) -> i32;

    fn dyn_clone(&self) -> Box<dyn DynConstraint<V>>;
}

impl<C, V> DynConstraint<V> for C
where
    V: SatVar,
    C: ConstraintRepr<V> + Clone + 'static,
{
    fn encode_repr(self: Box<Self>, solver: &mut ClauseCollector<V>) -> i32 {
        let this = *self;
        <Self as ConstraintRepr<V>>::encode_constraint_equals_repr(this, None, solver)
    }

    fn dyn_clone(&self) -> Box<dyn DynConstraint<V>> {
        Box::new(<Self as Clone>::clone(self))
    }
}

impl<V: SatVar> Expr<V> {
    fn encode_tree<E: Encoder<V>>(self, solver: &mut E) -> i32 {
        match self {
            Expr::Or(lhs, rhs) => {
                let lhs_var = lhs.encode_tree(solver);
                let rhs_var = rhs.encode_tree(solver);
                let new_var = solver.varmap().new_var();

                solver.add_clause(clause!(-new_var, lhs_var, rhs_var));
                solver.add_clause(clause!(new_var, -lhs_var));
                solver.add_clause(clause!(new_var, -rhs_var));

                new_var
            }
            Expr::And(lhs, rhs) => {
                let lhs_var = lhs.encode_tree(solver);
                let rhs_var = rhs.encode_tree(solver);
                let new_var = solver.varmap().new_var();

                solver.add_clause(clause!(-new_var, lhs_var));
                solver.add_clause(clause!(-new_var, rhs_var));
                solver.add_clause(clause!(-lhs_var, -rhs_var, new_var));

                new_var
            }
            Expr::Not(e) => {
                let new_var = solver.varmap().new_var();
                let e = e.encode_tree(solver);
                solver.add_clause(clause!(-e, -new_var));
                solver.add_clause(clause!(e, new_var));
                new_var
            }
            Expr::Lit(e) => solver.varmap().add_var(e),
            Expr::Constraint(constraint) => {
                let mut collector = ClauseCollector::from(solver.varmap());
                let repr = constraint.0.encode_repr(&mut collector);

                for cls in collector.clauses {
                    solver.add_clause(cls.into_iter());
                }

                repr
            }
        }
    }
}

impl<V> From<Lit<V>> for Expr<V> {
    fn from(v: Lit<V>) -> Self {
        Self::Lit(v)
    }
}

impl<V, R: Into<Self>> BitAnd<R> for Expr<V> {
    type Output = Expr<V>;

    fn bitand(self, rhs: R) -> Self::Output {
        let rhs = rhs.into();
        Self::And(Box::new(self), Box::new(rhs))
    }
}

impl<V, R: Into<Self>> BitOr<R> for Expr<V> {
    type Output = Expr<V>;

    fn bitor(self, rhs: R) -> Self::Output {
        let rhs = rhs.into();
        Self::Or(Box::new(self), Box::new(rhs))
    }
}

impl<V> Not for Expr<V> {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self::Not(Box::new(self))
    }
}

impl<V: SatVar> Constraint<V> for Expr<V> {
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let v = self.encode_tree(solver);
        solver.add_clause(clause!(v));
    }
}

impl<V: SatVar> ConstraintRepr<V> for Expr<V> {
    fn encode_constraint_implies_repr<E: Encoder<V>>(
        self,
        repr: Option<i32>,
        solver: &mut E,
    ) -> i32 {
        let r = self.encode_tree(solver);

        if let Some(repr) = repr {
            solver.add_clause(clause!(repr, -r));
            solver.add_clause(clause!(-repr, r));
            repr
        } else {
            r
        }
    }

    fn encode_constraint_equals_repr<E: Encoder<V>>(
        self,
        repr: Option<i32>,
        solver: &mut E,
    ) -> i32 {
        self.encode_constraint_implies_repr(repr, solver)
    }
}

#[cfg(test)]
mod tests {
    use crate::{constraints::{AtMostK, test_util::retry_until_unsat}, prelude::*, VarType};

    use super::*;

    #[test]
    fn expr_and() {
        let lit = Expr::from(Pos(1));

        let expr = lit & Pos(2) & Pos(3);

        let mut solver = Solver::new();

        solver.add_constraint(expr);

        let res = retry_until_unsat(&mut solver, |model| {
            assert!(model.vars().filter(|l| matches!(l, Pos(_))).count() == 3)
        });
        assert_eq!(res, 1);
    }

    #[test]
    fn expr_or() {
        let lit = Expr::from(Pos(1));

        let expr = lit | Pos(2) | Pos(3);

        let mut solver = Solver::new();

        solver.add_constraint(expr);

        let res = retry_until_unsat(&mut solver, |model| {
            assert!(model.vars().filter(|l| matches!(l, Pos(_))).count() > 0);
        });
        assert_eq!(res, 7);
    }

    #[test]
    fn expr_neg() {
        let lit = Expr::from(Pos(1));

        let expr = !lit;

        let mut solver = Solver::new();

        solver.add_constraint(expr);

        let res = retry_until_unsat(&mut solver, |model| assert!(model.lit(Neg(1)).unwrap()));
        assert_eq!(res, 1);
    }

    #[test]
    fn expr_combined() {
        let lit = Expr::from(Pos(1));

        let expr = lit.clone() & Pos(2) | !lit & Pos(3);

        let mut solver = Solver::new();

        solver.add_constraint(expr);

        let res = retry_until_unsat(&mut solver, |model| {
            let (a, b, c) = (
                model.var(1).unwrap(),
                model.var(2).unwrap(),
                model.var(3).unwrap(),
            );
            assert!(a && b || !a && c);
        });
        assert_eq!(res, 4);
    }

    #[test]
    fn expr_constraint() {
        let vars = (0..5).map(Pos);
        let constraint = AtMostK { k: 3, lits: vars };

        let e = Expr::from_constraint(constraint) & Pos(3) & Neg(4);

        let mut solver = Solver::new();
        solver.add_constraint(e);

        let res = retry_until_unsat(&mut solver, |model| {
            assert!(model.lit(Neg(4)).unwrap());
            assert!(model.lit(Pos(3)).unwrap());

            assert!(model.vars().filter(|l| matches!(l, Pos(_))).count() <= 3);
        });
        assert_eq!(res, 7);
    }

    #[test]
    fn expr_implies_repr() {
        let lit = Expr::from(Pos(1));

        let expr = lit.clone() & Pos(2) | !lit & Pos(3);

        let mut solver = Solver::new();

        let repr = solver.varmap().new_var();
        expr.encode_constraint_equals_repr(Some(repr), &mut solver);

        let res = retry_until_unsat(&mut solver, |model| {
            let (a, b, c) = (
                model.var(1).unwrap(),
                model.var(2).unwrap(),
                model.var(3).unwrap(),
            );
            if a && b || !a && c {
                assert!(model.lit_internal(VarType::Unnamed(repr)));
            }
        });
        assert_eq!(res, 8);
    }

    #[test]
    fn expr_equals_repr() {
        let lit = Expr::from(Pos(1));

        let expr = lit.clone() & Pos(2) | !lit & Pos(3);

        let mut solver = Solver::new();

        let repr = solver.varmap().new_var();
        expr.encode_constraint_equals_repr(Some(repr), &mut solver);

        let res = retry_until_unsat(&mut solver, |model| {
            let (a, b, c) = (
                model.var(1).unwrap(),
                model.var(2).unwrap(),
                model.var(3).unwrap(),
            );
            if a && b || !a && c {
                assert!(model.lit_internal(VarType::Unnamed(repr)));
            } else {
                assert!(model.lit_internal(VarType::Unnamed(-repr)));
            }
        });
        assert_eq!(res, 8);
    }

    #[test]
    fn expr_constraint_implies_repr() {
        let vars = (0..5).map(Pos);
        let constraint = AtMostK { k: 3, lits: vars };

        let e = Expr::from_constraint(constraint) & Pos(3) & Neg(4);

        let mut solver = Solver::new();

        let repr = solver.varmap().new_var();
        e.encode_constraint_equals_repr(Some(repr), &mut solver);

        let res = retry_until_unsat(&mut solver, |model| {
            let a = model.lit(Neg(4)).unwrap();
            let b = model.lit(Pos(3)).unwrap();
            let c = model.vars().filter(|l| matches!(l, Pos(_))).count() <= 3;

            if a && b && c {
                assert!(model.lit_internal(VarType::Unnamed(repr)));
            }
        });
        assert_eq!(res, 32);
    }
}
