use std::{
    fmt::{self, Debug},
    ops::{BitAnd, BitOr, Not},
};

use super::util::ClauseCollector;
use crate::{clause, Backend, Constraint, ConstraintRepr, SatVar, VarMap, VarType};

/// [Tseytin Encoding](https://en.wikipedia.org/wiki/Tseytin_transformation) of propositional logic formulas.
///
/// Allows encoding of arbitrary boolean formulas.
/// It implements the [`BitAnd`], [`BitOr`] and [`Not`] traits, which should be used for
/// the construction of boolean formulas.
///
/// # Example
/// ```rust
/// # use satoxid::{CadicalEncoder, constraints::Expr, Lit};
/// #
/// # fn main() {
/// #
/// # let mut encoder = CadicalEncoder::new();
/// #
/// let expr = !(Expr::new("a") | "b") & "c"; // encoding the formula !(a | b) & c
/// encoder.add_constraint(expr);
///
/// let model = encoder.solve().unwrap();
/// assert!(model[Lit::Neg("a")]);
/// assert!(model[Lit::Neg("b")]);
/// assert!(model[Lit::Pos("c")]);
/// # }
/// ```
///
/// **NOTE:** If you just want to 'and' or 'or' a bunch of literals use [`And`](crate::constraints::And) or [`Or`](crate::constraints::Or) for more efficient encodings.
#[derive(Clone)]
pub struct Expr<V> {
    inner: ExprEnum<V>,
}

impl<V: SatVar> Expr<V> {
    /// Create new `Expr` from given constraint.
    pub fn from_constraint<C>(constraint: C) -> Self
    where
        C: ConstraintRepr<V> + 'static,
    {
        Self {
            inner: ExprEnum::Constraint(ExprConstraint::new(constraint)),
        }
    }
}

impl<V: SatVar> Expr<V> {
    /// Create new `Expr` from literal.
    pub fn new<L>(l: L) -> Self
    where
        L: Into<VarType<V>>,
    {
        Self {
            inner: ExprEnum::Lit(l.into()),
        }
    }
}

impl<V: SatVar> Constraint<V> for Expr<V> {
    fn encode<B: Backend>(self, backend: &mut B, varmap: &mut VarMap<V>) {
        self.inner.encode(backend, varmap)
    }
}

impl<V: SatVar> ConstraintRepr<V> for Expr<V> {
    fn encode_constraint_implies_repr<B: Backend>(
        self,
        repr: Option<i32>,
        backend: &mut B,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        self.inner
            .encode_constraint_implies_repr(repr, backend, varmap)
    }

    fn encode_constraint_equals_repr<B: Backend>(
        self,
        repr: Option<i32>,
        backend: &mut B,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        self.inner
            .encode_constraint_equals_repr(repr, backend, varmap)
    }

    fn encode_constraint_repr_cheap<B: Backend>(
        self,
        repr: Option<i32>,
        backend: &mut B,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        self.inner
            .encode_constraint_repr_cheap(repr, backend, varmap)
    }
}

impl<V: SatVar, L: Into<VarType<V>>> From<L> for Expr<V> {
    fn from(l: L) -> Self {
        Self {
            inner: ExprEnum::Lit(l.into()),
        }
    }
}

impl<V, R: Into<Self>> BitAnd<R> for Expr<V> {
    type Output = Expr<V>;

    fn bitand(self, rhs: R) -> Self::Output {
        let rhs = rhs.into();
        Self {
            inner: ExprEnum::And(Box::new(self.inner), Box::new(rhs.inner)),
        }
    }
}

impl<V, R: Into<Self>> BitOr<R> for Expr<V> {
    type Output = Expr<V>;

    fn bitor(self, rhs: R) -> Self::Output {
        let rhs = rhs.into();
        Self {
            inner: ExprEnum::Or(Box::new(self.inner), Box::new(rhs.inner)),
        }
    }
}

impl<V> Not for Expr<V> {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self {
            inner: ExprEnum::Not(Box::new(self.inner)),
        }
    }
}

impl<V: Debug> Debug for Expr<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.inner.fmt(f)
    }
}

#[derive(Clone)]
enum ExprEnum<V> {
    And(Box<ExprEnum<V>>, Box<ExprEnum<V>>),
    Or(Box<ExprEnum<V>>, Box<ExprEnum<V>>),
    Not(Box<ExprEnum<V>>),
    Lit(VarType<V>),
    Constraint(ExprConstraint<V>),
}

impl<V: Debug> Debug for ExprEnum<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExprEnum::And(lhs, rhs) => {
                f.debug_tuple("And").field(&lhs).field(&rhs).finish()
            }
            ExprEnum::Or(lhs, rhs) => {
                f.debug_tuple("Or").field(&lhs).field(&rhs).finish()
            }
            ExprEnum::Not(e) => f.debug_tuple("Neg").field(&e).finish(),
            ExprEnum::Lit(lit) => f.debug_tuple("Lit").field(&lit).finish(),
            ExprEnum::Constraint(constraint) => {
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

trait DynConstraint<V>: Debug {
    fn encode_repr(
        self: Box<Self>,
        solver: &mut ClauseCollector,
        varmap: &mut VarMap<V>,
    ) -> i32;

    fn dyn_clone(&self) -> Box<dyn DynConstraint<V>>;
}

impl<C, V> DynConstraint<V> for C
where
    V: SatVar,
    C: ConstraintRepr<V> + Clone + 'static,
{
    fn encode_repr(
        self: Box<Self>,
        solver: &mut ClauseCollector,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let this = *self;
        <Self as ConstraintRepr<V>>::encode_constraint_equals_repr(
            this, None, solver, varmap,
        )
    }

    fn dyn_clone(&self) -> Box<dyn DynConstraint<V>> {
        Box::new(<Self as Clone>::clone(self))
    }
}

impl<V: SatVar> ExprEnum<V> {
    fn encode_tree<B: Backend>(self, backend: &mut B, varmap: &mut VarMap<V>) -> i32 {
        match self {
            ExprEnum::Or(lhs, rhs) => {
                let lhs_var = lhs.encode_tree(backend, varmap);
                let rhs_var = rhs.encode_tree(backend, varmap);
                let new_var = varmap.new_var();

                backend.add_clause(clause!(-new_var, lhs_var, rhs_var));
                backend.add_clause(clause!(new_var, -lhs_var));
                backend.add_clause(clause!(new_var, -rhs_var));

                new_var
            }
            ExprEnum::And(lhs, rhs) => {
                let lhs_var = lhs.encode_tree(backend, varmap);
                let rhs_var = rhs.encode_tree(backend, varmap);
                let new_var = varmap.new_var();

                backend.add_clause(clause!(-new_var, lhs_var));
                backend.add_clause(clause!(-new_var, rhs_var));
                backend.add_clause(clause!(-lhs_var, -rhs_var, new_var));

                new_var
            }
            ExprEnum::Not(e) => {
                let new_var = varmap.new_var();
                let e = e.encode_tree(backend, varmap);
                backend.add_clause(clause!(-e, -new_var));
                backend.add_clause(clause!(e, new_var));
                new_var
            }
            ExprEnum::Lit(e) => varmap.add_var(e),
            ExprEnum::Constraint(constraint) => {
                let mut collector = ClauseCollector::default();
                let repr = constraint.0.encode_repr(&mut collector, varmap);

                for cls in collector.clauses {
                    backend.add_clause(cls.into_iter());
                }

                repr
            }
        }
    }
}

impl<V: SatVar> Constraint<V> for ExprEnum<V> {
    fn encode<B: Backend>(self, backend: &mut B, varmap: &mut VarMap<V>) {
        let v = self.encode_tree(backend, varmap);
        backend.add_clause(clause!(v));
    }
}

impl<V: SatVar> ConstraintRepr<V> for ExprEnum<V> {
    fn encode_constraint_implies_repr<B: Backend>(
        self,
        repr: Option<i32>,
        backend: &mut B,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let r = self.encode_tree(backend, varmap);

        // Since `r` is always equal to the satisfiability of the expression,
        // we need to always use a new repr and form an implication.
        let repr = repr.unwrap_or_else(|| varmap.new_var());

        backend.add_clause(clause!(-r, repr));

        repr
    }

    fn encode_constraint_equals_repr<B: Backend>(
        self,
        repr: Option<i32>,
        backend: &mut B,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let r = self.encode_tree(backend, varmap);

        if let Some(repr) = repr {
            backend.add_clause(clause!(repr, -r));
            backend.add_clause(clause!(-repr, r));
            repr
        } else {
            r
        }
    }

    fn encode_constraint_repr_cheap<B: Backend>(
        self,
        repr: Option<i32>,
        backend: &mut B,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        self.encode_constraint_equals_repr(repr, backend, varmap)
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
            AtLeastK, AtMostK,
        },
        CadicalEncoder,
        Lit::*,
    };

    #[test]
    fn expr_and() {
        let lit = Expr::from(1);

        let expr = lit & 2 & 3;

        let mut encoder = CadicalEncoder::<u32>::new();

        encoder.add_constraint(expr);

        let res = retry_until_unsat(&mut encoder, |model| {
            assert!(model.vars().filter(|l| l.is_pos()).count() == 3)
        });
        assert_eq!(res, 1);
    }

    #[test]
    fn expr_or() {
        let lit = Expr::from(1);

        let expr = lit | 2 | 3;

        let mut encoder = CadicalEncoder::<u32>::new();

        encoder.add_constraint(expr);

        let res = retry_until_unsat(&mut encoder, |model| {
            assert!(model.vars().filter(|l| l.is_pos()).count() > 0);
        });
        assert_eq!(res, 7);
    }

    #[test]
    fn expr_neg() {
        let lit = Expr::from(1);

        let expr = !lit;

        let mut encoder = CadicalEncoder::<u32>::new();

        encoder.add_constraint(expr);

        let res = retry_until_unsat(&mut encoder, |model| {
            assert!(model.lit(Neg(1)).unwrap())
        });
        assert_eq!(res, 1);
    }

    #[test]
    fn expr_combined() {
        let lit = Expr::from(1);

        let expr = lit.clone() & 2 | !lit & 3;

        let mut encoder = CadicalEncoder::<u32>::new();

        encoder.add_constraint(expr);

        let res = retry_until_unsat(&mut encoder, |model| {
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
        let vars = 0..5;
        let constraint = AtMostK { k: 3, lits: vars };

        let e = Expr::from_constraint(constraint) & 3 & Neg(4);

        let mut encoder = CadicalEncoder::<u32>::new();
        encoder.add_constraint(e);

        let res = retry_until_unsat(&mut encoder, |model| {
            assert!(model.lit(Neg(4)).unwrap());
            assert!(model.lit(Pos(3)).unwrap());

            assert!(model.vars().filter(|l| l.is_pos()).count() <= 3);
        });
        assert_eq!(res, 7);
    }

    #[test]
    fn expr_implies_repr() {
        let lit = Expr::from(1);

        let expr = lit.clone() & 2 | !lit & 3;

        let mut encoder = CadicalEncoder::new();

        let repr = encoder.varmap.new_var();
        expr.encode_constraint_implies_repr(
            Some(repr),
            &mut encoder.backend,
            &mut encoder.varmap,
        );

        let res = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            let (a, b, c) = (
                model.var(1).unwrap(),
                model.var(2).unwrap(),
                model.var(3).unwrap(),
            );
            a && b || !a && c
        });
        assert_eq!(res.correct, 4);
        assert_eq!(res.total(), 8);
    }

    #[test]
    fn expr_equals_repr() {
        let lit = Expr::from(1);

        let expr = lit.clone() & 2 | !lit & 3;

        let mut encoder = CadicalEncoder::<u32>::new();

        let repr = encoder.varmap.new_var();
        expr.encode_constraint_equals_repr(
            Some(repr),
            &mut encoder.backend,
            &mut encoder.varmap,
        );

        let res = constraint_equals_repr_tester(&mut encoder, repr, |model| {
            let (a, b, c) = (
                model.var(1).unwrap(),
                model.var(2).unwrap(),
                model.var(3).unwrap(),
            );
            a && b || !a && c
        });
        assert_eq!(res.correct, 4);
        assert_eq!(res.total(), 8);
    }

    #[test]
    fn expr_constraint_implies_repr() {
        let range = 5;
        let k = 3;
        let vars = 0..range;
        let constraint = AtMostK { k, lits: vars };

        let e = Expr::from_constraint(constraint) & Pos(3) & Neg(4);

        let mut encoder = CadicalEncoder::<u32>::new();

        let repr = encoder.varmap.new_var();
        e.encode_constraint_implies_repr(
            Some(repr),
            &mut encoder.backend,
            &mut encoder.varmap,
        );

        let res = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            let a = model.lit(Neg(4)).unwrap();
            let b = model.lit(Pos(3)).unwrap();
            let c = model.vars().filter(|l| l.is_pos()).count() <= 3;

            a && b && c
        });
        assert_eq!(
            res.correct as u32,
            (0..k).map(|i| binomial(3, i)).sum::<u32>()
        );
        assert_eq!(res.total(), 1 << 5)
    }

    #[test]
    fn expr_constraint_or() {
        let range = 4;
        let vars = 0..range;

        let empty_cond = AtMostK {
            k: 0,
            lits: vars.clone(),
        };
        let filled_cond = AtLeastK { k: 3, lits: vars };

        let e =
            Expr::from_constraint(filled_cond) | Expr::from_constraint(empty_cond);

        let mut encoder = CadicalEncoder::<u32>::new();

        encoder.add_constraint(e);

        let res = retry_until_unsat(&mut encoder, |model| {
            model.print_model();
            let empty_cond = model.vars().filter(|l| l.is_pos()).count() == 0;
            let filled_cond = model.vars().filter(|l| l.is_pos()).count() >= 3;

            assert!(filled_cond | empty_cond);
        });
        assert_eq!(res, binomial(4, 0) + binomial(4, 3) + binomial(4, 4));
    }
}
