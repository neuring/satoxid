//! Collection of commonly used constraints.

use core::fmt;
use std::fmt::Debug;

use super::{Constraint, SatVar, VarMap};
use crate::{Backend, ConstraintRepr, VarType};

mod cardinality;
mod conditional;
mod expr;
pub(crate) mod util;

#[cfg(test)]
mod test_util;

pub use cardinality::{
    AtLeastK, AtMostK, ExactlyK, LessCardinality, SameCardinality,
};
pub use conditional::{If, Iff};
pub use expr::Expr;

#[doc(hidden)]
#[macro_export]
macro_rules! clause {
    ($($e:expr),*) => {
        [$($e),*].iter().copied()
    }
}

impl<V, L> Constraint<V> for L
where
    V: SatVar,
    L: Debug + Clone + Into<VarType<V>>,
{
    fn encode<B: Backend>(self, backend: &mut B, varmap: &mut VarMap<V>) {
        let var = varmap.add_var(self);
        backend.add_clause(clause!(var));
    }
}

impl<V, L> ConstraintRepr<V> for L
where
    V: SatVar,
    L: Debug + Clone + Into<VarType<V>>,
{
    fn encode_constraint_implies_repr<B: Backend>(
        self,
        repr: Option<i32>,
        backend: &mut B,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| varmap.new_var());
        let var = varmap.add_var(self);

        backend.add_clause(clause![-var, repr]);

        repr
    }

    fn encode_constraint_equals_repr<B: Backend>(
        self,
        repr: Option<i32>,
        backend: &mut B,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let var = varmap.add_var(self);

        if let Some(repr) = repr {
            backend.add_clause(clause![-var, repr]);
            backend.add_clause(clause![var, -repr]);
            repr
        } else {
            var
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

/// Constraint which represents a simple clause.
///
/// # Example
/// ```rust
/// # use satoxid::{CadicalEncoder, constraints::Or};
/// # fn main() {
/// # let mut encoder = CadicalEncoder::new();
/// let constraint = Or(vec!["a", "b", "c"].into_iter());
///
/// encoder.add_constraint(constraint);
///
/// let model = encoder.solve().unwrap();
/// assert!(model["a"] || model["b"] || model["c"]);
/// # }
/// ```
#[derive(Clone)]
pub struct Or<I>(pub I);

impl<I, V> Constraint<V> for Or<I>
where
    V: SatVar,
    I: Iterator + Clone,
    I::Item: Into<VarType<V>> + Debug,
{
    fn encode<B: Backend>(self, backend: &mut B, varmap: &mut VarMap<V>) {
        backend.add_clause(self.0.map(|lit| varmap.add_var(lit.into())));
    }
}

impl<I, V> ConstraintRepr<V> for Or<I>
where
    V: SatVar,
    I: Iterator + Clone,
    I::Item: Into<VarType<V>> + Debug,
{
    fn encode_constraint_implies_repr<B: Backend>(
        self,
        repr: Option<i32>,
        backend: &mut B,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| varmap.new_var());

        for lit in self.0 {
            let sat_lit = varmap.add_var(lit);

            backend.add_clause(clause![-sat_lit, repr]);
        }

        repr
    }
}

impl<I> Debug for Or<I>
where
    I: Iterator + Clone,
    I::Item: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list: Vec<_> = self.0.clone().collect();
        f.debug_tuple("Or").field(&list).finish()
    }
}

/// Constraint which requires all literals to be true.
///
/// # Example
/// ```rust
/// # use satoxid::{CadicalEncoder, constraints::And};
/// # fn main() {
/// # let mut encoder = CadicalEncoder::new();
/// let constraint = And(vec!["a", "b", "c"].into_iter());
///
/// encoder.add_constraint(constraint);
///
/// let model = encoder.solve().unwrap();
/// assert!(model["a"] && model["b"] && model["c"]);
/// # }
/// ```
#[derive(Clone)]
pub struct And<I>(pub I);

impl<V, I> Constraint<V> for And<I>
where
    V: SatVar,
    I: Iterator + Clone,
    I::Item: Into<VarType<V>> + Debug,
{
    fn encode<B: Backend>(self, backend: &mut B, varmap: &mut VarMap<V>) {
        for v in self.0 {
            let v = varmap.add_var(v);
            backend.add_clause(clause![v]);
        }
    }
}

impl<V, I> ConstraintRepr<V> for And<I>
where
    V: SatVar,
    I: Iterator + Clone,
    I::Item: Into<VarType<V>> + Debug,
{
    fn encode_constraint_implies_repr<B: Backend>(
        self,
        repr: Option<i32>,
        backend: &mut B,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| varmap.new_var());

        let vars = self.0.map(|l| -varmap.add_var(l));
        backend.add_clause(vars.chain(clause![repr]));

        repr
    }
}

impl<I> Debug for And<I>
where
    I: Iterator + Clone,
    I::Item: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list: Vec<_> = self.0.clone().collect();
        f.debug_tuple("And").field(&list).finish()
    }
}

/// Constraint which requires all literals to be same value.
///
/// # Example
/// ```rust
/// # use satoxid::{CadicalEncoder, constraints::Equal};
/// # fn main() {
/// # let mut encoder = CadicalEncoder::new();
/// let constraint = Equal(vec!["a", "b", "c"].into_iter());
///
/// encoder.add_constraint(constraint);
///
/// let model = encoder.solve().unwrap();
/// assert!(model["a"] == model["b"] && model["a"] == model["b"]);
/// # }
/// ```
#[derive(Clone)]
pub struct Equal<I>(pub I);

impl<V, I> Constraint<V> for Equal<I>
where
    V: SatVar,
    I: Iterator + Clone,
    I::Item: Into<VarType<V>> + Debug,
{
    fn encode<B: Backend>(self, backend: &mut B, varmap: &mut VarMap<V>) {
        let lits: Vec<_> = self.0.map(|l| varmap.add_var(l)).collect();

        for l in lits.windows(2) {
            backend.add_clause(clause![-l[0], l[1]]);
        }

        backend.add_clause(clause![-lits[lits.len() - 1], lits[0]]);
    }
}

impl<V, I> ConstraintRepr<V> for Equal<I>
where
    V: SatVar,
    I: Iterator + Clone,
    I::Item: Into<VarType<V>> + Debug,
{
    fn encode_constraint_implies_repr<B: Backend>(
        self,
        repr: Option<i32>,
        backend: &mut B,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| varmap.new_var());
        let lits: Vec<_> = self.0.map(|l| varmap.add_var(l)).collect();

        backend.add_clause(lits.iter().copied().chain(clause![repr]));
        backend.add_clause(lits.into_iter().map(|l| -l).chain(clause![repr]));

        repr
    }
}

impl<I> Debug for Equal<I>
where
    I: Iterator + Clone,
    I::Item: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list: Vec<_> = self.0.clone().collect();
        f.debug_tuple("Equal").field(&list).finish()
    }
}

/// Constraint which inverts a constraint.
/// If a constraint `C` is unsatisfiable than `Not(C)` is satisfiable and vice versa.
///
/// # Example
/// ```rust
/// # use satoxid::{CadicalEncoder, Lit, constraints::{Not, Or}};
/// # fn main() {
/// # let mut encoder = CadicalEncoder::new();
/// let constraint = Not(Or(vec!["a", "b", "c"].into_iter()));
///
/// encoder.add_constraint(constraint);
///
/// let model = encoder.solve().unwrap();
/// assert!(model[Lit::Neg("a")] && model[Lit::Neg("b")] && model[Lit::Neg("c")]);
/// # }
#[derive(Debug, Clone)]
pub struct Not<C>(pub C);

impl<V, C> Constraint<V> for Not<C>
where
    V: SatVar,
    C: ConstraintRepr<V>,
{
    fn encode<B: Backend>(self, backend: &mut B, varmap: &mut VarMap<V>) {
        let repr = self.0.encode_constraint_implies_repr(None, backend, varmap);

        backend.add_clause(clause![-repr]);
    }
}

impl<V, C> ConstraintRepr<V> for Not<C>
where
    V: SatVar,
    C: ConstraintRepr<V>,
{
    fn encode_constraint_implies_repr<B: Backend>(
        self,
        repr: Option<i32>,
        backend: &mut B,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let not_repr = repr.unwrap_or_else(|| varmap.new_var());
        let repr = self.0.encode_constraint_equals_repr(None, backend, varmap);

        backend.add_clause(clause![repr, not_repr]);

        not_repr
    }

    fn encode_constraint_equals_repr<B: Backend>(
        self,
        repr: Option<i32>,
        backend: &mut B,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let not_repr = repr.unwrap_or_else(|| varmap.new_var());
        let repr = self.0.encode_constraint_equals_repr(None, backend, varmap);

        backend.add_clause(clause![repr, not_repr]);
        backend.add_clause(clause![-repr, -not_repr]);

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
    use crate::{CadicalEncoder, ConstraintRepr, Lit};

    use num_integer::binomial;

    #[test]
    fn lit_implies_repr() {
        let mut encoder = CadicalEncoder::new();

        let lit = Lit::Pos(1);

        let repr = encoder.varmap.new_var();
        let r = lit.encode_constraint_implies_repr(
            Some(repr),
            &mut encoder.backend,
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
        let mut encoder = CadicalEncoder::new();

        let lit = Lit::Pos(1);

        let repr = lit.encode_constraint_implies_repr(
            None,
            &mut encoder.backend,
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
        let mut encoder = CadicalEncoder::new();

        let lit = Lit::Pos(1);

        let repr = encoder.varmap.new_var();
        let r = lit.encode_constraint_equals_repr(
            Some(repr),
            &mut encoder.backend,
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
        let mut encoder = CadicalEncoder::<u32>::new();

        let range = 6;
        let clause = Or((1..=range).map(Lit::Pos));

        let r = clause.encode_constraint_implies_repr(
            None,
            &mut encoder.backend,
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
        let mut encoder = CadicalEncoder::<u32>::new();

        let range = 6;
        let clause = Or((1..=range).map(Lit::Pos));

        let r = clause.encode_constraint_equals_repr(
            None,
            &mut encoder.backend,
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
        let mut encoder = CadicalEncoder::<usize>::new();

        let range = 6;
        let constraint = And((1..=range).map(Lit::Pos));

        let r = constraint.encode_constraint_implies_repr(
            None,
            &mut encoder.backend,
            &mut encoder.varmap,
        );

        let res = constraint_implies_repr_tester(&mut encoder, r, |model| {
            model.vars().filter(|l| matches!(l, Lit::Pos(_))).count() == range
        });
        assert_eq!(res.correct, 1);
        assert_eq!(res.total(), (1 << range));
    }

    #[test]
    fn and_equals_repr() {
        let mut encoder = CadicalEncoder::<usize>::new();

        let range = 6;
        let constraint = And((1..=range).map(Lit::Pos));

        let r = constraint.encode_constraint_equals_repr(
            None,
            &mut encoder.backend,
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
        let mut encoder = CadicalEncoder::<u32>::new();

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
        let mut encoder = CadicalEncoder::<u32>::new();

        let range = 6;
        let constraint = Equal((1..=range).map(Lit::Pos));

        let r = constraint.encode_constraint_implies_repr(
            None,
            &mut encoder.backend,
            &mut encoder.varmap,
        );

        let res = constraint_implies_repr_tester(&mut encoder, r, |model| {
            model.vars().all(|l| matches!(l, Lit::Pos(_)))
                || model.vars().all(|l| matches!(l, Lit::Neg(_)))
        });
        assert_eq!(res.correct, 2);
        assert_eq!(res.total(), (1 << range));
    }

    #[test]
    fn equal_equals_repr() {
        let mut encoder = CadicalEncoder::<u32>::new();

        let range = 6;
        let constraint = Equal((1..=range).map(Lit::Pos));

        let r = constraint.encode_constraint_equals_repr(
            None,
            &mut encoder.backend,
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
        let mut encoder = CadicalEncoder::<u32>::new();

        let range = 6;
        let k = 3;
        let constraint = AtLeastK {
            k,
            lits: (0..range).map(Lit::Pos),
        };

        let constraint = Not(constraint);

        encoder.add_constraint(constraint);

        let res = retry_until_unsat(&mut encoder, |model| {
            assert!(
                model.vars().filter(|l| matches!(l, Lit::Pos(_))).count()
                    < k as usize
            );
        });
        assert_eq!(res as u32, (0..k).map(|i| binomial(range, i)).sum::<u32>());
    }

    #[test]
    fn not_implies_repr() {
        let mut encoder = CadicalEncoder::<u32>::new();

        let range = 6;
        let k = 3;
        let constraint = AtLeastK {
            k,
            lits: (0..range).map(Lit::Pos),
        };

        let constraint = Not(constraint);

        let repr = constraint.encode_constraint_implies_repr(
            None,
            &mut encoder.backend,
            &mut encoder.varmap,
        );

        let res = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            model.vars().filter(|l| matches!(l, Lit::Pos(_))).count() < k as usize
        });
        assert_eq!(
            res.correct as u32,
            (0..k).map(|i| binomial(range, i)).sum::<u32>()
        );
        assert_eq!(res.total() as u32, 1 << range);
    }

    #[test]
    fn not_equals_repr() {
        let mut encoder = CadicalEncoder::<u32>::new();

        let range = 6;
        let k = 3;
        let constraint = AtLeastK {
            k,
            lits: (0..range).map(Lit::Pos),
        };

        let constraint = Not(constraint);

        let repr = constraint.encode_constraint_equals_repr(
            None,
            &mut encoder.backend,
            &mut encoder.varmap,
        );

        let res = constraint_equals_repr_tester(&mut encoder, repr, |model| {
            model.vars().filter(|l| matches!(l, Lit::Pos(_))).count() < k as usize
        });
        assert_eq!(
            res.correct as u32,
            (0..k).map(|i| binomial(range, i)).sum::<u32>()
        );
        assert_eq!(res.total() as u32, 1 << range);
    }
}
