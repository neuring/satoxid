use core::fmt;
use std::{fmt::Debug, iter::once};

use crate::circuit::{Circuit, Direction};
use crate::{
    clause, Constraint, ConstraintRepr, Encoder, Lit, SatVar, Solver, VarMap,
};

/// Encodes a sequential counter used for all cardinality constraint types.
/// Returns the k output vars which different constraints can constrain to
/// achieve their respective behaviour.
fn encode_cardinality_constraint<V, S, I>(
    lits: I,
    k: u32,
    dir: Direction,
    solver: &mut S,
    varmap: &mut VarMap<V>,
) -> Vec<i32>
where
    V: SatVar,
    S: Solver,
    I: Iterator<Item = Lit<V>>,
{
    assert!(k > 0);

    let mut circuit = Circuit::new(solver, dir);

    let vars: Vec<_> = lits.map(|v| varmap.add_var(v)).collect();
    let n = vars.len();

    let mut prev_s: Vec<_> = (0..k).map(|_| varmap.new_var()).collect();

    if let Some(&v) = vars.first() {
        circuit.equal(v, prev_s[0]);
    } else {
        panic!("No variables to encode");
    }

    for &s in prev_s.iter().skip(1) {
        circuit.set_zero(s);
    }

    for (i, &v) in vars.iter().enumerate().skip(1) {
        let new_s: Vec<_> = (0..k).map(|_| varmap.new_var()).collect();

        circuit.or_gate(clause![v, prev_s[0]], new_s[0]);

        for j in 1..(k as usize) {
            let a = varmap.new_var();

            circuit.and_gate(clause![v, prev_s[j - 1]], a);
            circuit.or_gate(clause![a, prev_s[j]], new_s[j]);
        }

        prev_s = new_s;
    }

    prev_s
}

/// This constraint encodes the requirement that at most `k` of `lits` variables
/// are true.
#[derive(Clone)]
pub struct AtMostK<I> {
    pub lits: I,
    pub k: u32,
}

impl<V, I> Constraint<V> for AtMostK<I>
where
    V: SatVar + Clone + Debug,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode<S: Solver>(self, solver: &mut S, varmap: &mut VarMap<V>) {
        if self.k == 0 {
            for v in self.lits {
                let v = varmap.add_var(v);
                solver.add_clause(clause![-v]);
            }
        } else {
            let out = encode_cardinality_constraint(
                self.lits,
                self.k + 1,
                Direction::InToOut,
                solver,
                varmap,
            );

            solver.add_clause(clause![-out.last().unwrap()]);
        }
    }
}

impl<V, I> ConstraintRepr<V> for AtMostK<I>
where
    V: SatVar,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode_constraint_implies_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        if self.k == 0 {
            let repr = repr.unwrap_or_else(|| varmap.new_var());

            let lits = self.lits.map(|lit| varmap.add_var(lit));
            solver.add_clause(lits.chain(clause![repr]));

            repr
        } else {
            let out = encode_cardinality_constraint(
                self.lits,
                self.k + 1,
                Direction::OutToIn,
                solver,
                varmap,
            );

            let r = -out.last().unwrap();
            dbg!(r);

            if let Some(repr) = repr {
                solver.add_clause(clause![r, repr]);
                solver.add_clause(clause![-r, -repr]);
                repr
            } else {
                r
            }
        }
    }

    fn encode_constraint_equals_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        if self.k == 0 {
            let repr = repr.unwrap_or_else(|| varmap.new_var());

            let lits = self.lits.clone().map(|lit| varmap.add_var(lit));
            solver.add_clause(lits.chain(clause![repr]));

            let lits = self.lits.map(|lit| varmap.add_var(lit));
            for lit in lits {
                solver.add_clause(clause![-lit, -repr])
            }

            repr
        } else {
            let out = encode_cardinality_constraint(
                self.lits,
                self.k + 1,
                Direction::Both,
                solver,
                varmap,
            );

            let r = -out.last().unwrap();
            dbg!(r);

            if let Some(repr) = repr {
                solver.add_clause(clause![r, repr]);
                solver.add_clause(clause![-r, -repr]);
                repr
            } else {
                r
            }
        }
    }
}

impl<V: Debug, I> Debug for AtMostK<I>
where
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<_> = self.lits.clone().collect();

        f.debug_struct("AtMostK")
            .field("k", &self.k)
            .field("vars", &lits)
            .finish()
    }
}

/// This constraint encodes the requirement that atleast `k` of `lits` variables
/// are true.
#[derive(Clone)]
pub struct AtleastK<I> {
    pub lits: I,
    pub k: u32,
}

impl<V, I> Constraint<V> for AtleastK<I>
where
    V: SatVar,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode<S: Solver>(self, solver: &mut S, varmap: &mut VarMap<V>) {
        if self.k == 0 {
            return;
        } else {
            let out = encode_cardinality_constraint(
                self.lits,
                self.k,
                Direction::OutToIn,
                solver,
                varmap,
            );

            solver.add_clause(clause![*out.last().unwrap()]);
        }
    }
}

impl<V, I> ConstraintRepr<V> for AtleastK<I>
where
    V: SatVar,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode_constraint_implies_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        if self.k == 0 {
            let repr = repr.unwrap_or_else(|| varmap.new_var());

            solver.add_clause(clause![repr]);

            repr
        } else {
            let out = encode_cardinality_constraint(
                self.lits,
                self.k,
                Direction::InToOut,
                solver,
                varmap,
            );

            let r = *out.last().unwrap();

            if let Some(repr) = repr {
                solver.add_clause(clause![r, repr]);
                solver.add_clause(clause![-r, -repr]);
                repr
            } else {
                r
            }
        }
    }

    fn encode_constraint_equals_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        if self.k == 0 {
            let repr = repr.unwrap_or_else(|| varmap.new_var());

            solver.add_clause(clause![repr]);

            repr
        } else {
            let out = encode_cardinality_constraint(
                self.lits,
                self.k,
                Direction::Both,
                solver,
                varmap,
            );

            let r = *out.last().unwrap();

            if let Some(repr) = repr {
                solver.add_clause(clause![r, repr]);
                solver.add_clause(clause![-r, -repr]);
                repr
            } else {
                r
            }
        }
    }
}

impl<V: Debug, I> Debug for AtleastK<I>
where
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<_> = self.lits.clone().collect();

        f.debug_struct("AtleastK")
            .field("k", &self.k)
            .field("vars", &lits)
            .finish()
    }
}

/// This constraint encodes the requirement that exactly `k` of `lits` variables
/// are true.
#[derive(Clone)]
pub struct ExactlyK<I> {
    pub lits: I,
    pub k: u32,
}

impl<V, I> Constraint<V> for ExactlyK<I>
where
    V: SatVar + Clone + Debug,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode<S: Solver>(self, solver: &mut S, varmap: &mut VarMap<V>) {
        if self.k == 0 {
            for v in self.lits {
                let v = varmap.add_var(v);
                solver.add_clause(clause![-v]);
            }
        } else {
            let out = encode_cardinality_constraint(
                self.lits,
                self.k + 1,
                Direction::Both,
                solver,
                varmap,
            );

            solver.add_clause(clause![out[out.len() - 2]]);
            solver.add_clause(clause![-out[out.len() - 1]]);
        }
    }
}

impl<V, I> ConstraintRepr<V> for ExactlyK<I>
where
    V: SatVar,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode_constraint_implies_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| varmap.new_var());

        if self.k == 0 {

            let lits = self.lits.map(|lit| varmap.add_var(lit));
            solver.add_clause(lits.chain(clause![repr]));

        } else {
            let out = encode_cardinality_constraint(
                self.lits,
                self.k + 1,
                Direction::Both,
                solver,
                varmap,
            );

            let r1 = out[out.len() - 2];
            let r2 = out[out.len() - 1];

            solver.add_clause(clause!(-r1, r2, repr));

        }

        repr
    }

    fn encode_constraint_equals_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| varmap.new_var());

        if self.k == 0 {

            let lits = self.lits.clone().map(|lit| varmap.add_var(lit));
            solver.add_clause(lits.chain(clause![repr]));

            let lits = self.lits.map(|lit| varmap.add_var(lit));
            for lit in lits {
                solver.add_clause(clause![-lit, -repr])
            }

        } else {
            let out = encode_cardinality_constraint(
                self.lits,
                self.k + 1,
                Direction::Both,
                solver,
                varmap,
            );

            let r1 = out[out.len() - 2];
            let r2 = out[out.len() - 1];

            solver.add_clause(clause!(-r1, r2, repr));
            solver.add_clause(clause!(r1, -repr));
            solver.add_clause(clause!(-r2, -repr));

        }
            repr
    }
}

impl<V: Debug, I> Debug for ExactlyK<I>
where
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<_> = self.lits.clone().collect();

        f.debug_struct("ExactlyK")
            .field("k", &self.k)
            .field("vars", &lits)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use num_integer::binomial;

    use crate::{
        constraints::{
            test_util::{
                constraint_equals_repr_tester, constraint_implies_repr_tester,
                retry_until_unsat,
            },
            Clause, Equal,
        },
        prelude::*,
        Solver, VarType,
    };

    use super::*;

    #[test]
    fn normal_atmostk() {
        let mut encoder = DefaultEncoder::new();

        let range = 10;
        let k = 5;
        let lits = (1..=range).map(|i| Pos(i));

        encoder.add_constraint(AtMostK { k, lits });

        let models = retry_until_unsat(&mut encoder, |model| {
            model.print_model();
            assert!(model.vars().filter(|l| l.is_pos()).count() <= k as usize)
        });
        assert_eq!(models as u32, (0..=k).map(|i| binomial(range, i)).sum());
    }

    #[test]
    fn normal_atmost0() {
        let mut encoder = DefaultEncoder::new();

        let lits = (1..=10).map(|i| Pos(i));
        let k = 0;

        encoder.add_constraint(AtMostK { k, lits });

        let models = retry_until_unsat(&mut encoder, |model| {
            model.print_model();
            assert!(model.vars().filter(|l| l.is_pos()).count() <= k as usize)
        });
        assert_eq!(models, 1);
    }

    #[test]
    fn atmostk_implies_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 10;
        let k = 5;
        let lits = (1..=range).map(|i| Pos(i));
        let constraint = AtMostK { k, lits };

        let repr = constraint.encode_constraint_implies_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );
        assert_ne!(repr, 0);

        let res = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            model.vars().filter(|l| l.is_pos()).count() <= k as usize
        });
        assert_eq!(
            res.correct as u32,
            (0..=k).map(|i| binomial(range, i)).sum()
        );
        assert_eq!(res.total(), 1 << range);
    }

    #[test]
    fn atmostk_equals_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 10;
        let k = 5;
        let lits = (1..=range).map(|i| Pos(i));

        let constraint = AtMostK { k, lits };

        let repr = constraint.encode_constraint_equals_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );

        let res = constraint_equals_repr_tester(&mut encoder, repr, |model| {
            model.print_model();
            model.vars().filter(|l| l.is_pos()).count() <= k as usize
        });
        assert_eq!(
            res.correct as u32,
            (0..=k).map(|i| binomial(range, i)).sum()
        );
        assert_eq!(res.total(), 1 << range);
    }

    #[test]
    fn atmost0_implies_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 10;
        let k = 0;
        let lits = (1..=range).map(|i| Pos(i));

        let constraint = AtMostK { k, lits };

        let repr = encoder.varmap.new_var();
        constraint.encode_constraint_implies_repr(
            Some(repr),
            &mut encoder.solver,
            &mut encoder.varmap,
        );

        let res = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            model.vars().filter(|l| l.is_pos()).count() <= k as usize
        });
        assert_eq!(res.correct, 1);
        assert_eq!(res.total(), 1 << range);
    }

    #[test]
    fn atmost0_equals_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 10;
        let k = 0;
        let lits = (1..=range).map(|i| Pos(i));

        let constraint = AtMostK { k, lits };

        let repr = constraint.encode_constraint_equals_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );

        let res = constraint_equals_repr_tester(&mut encoder, repr, |model| {
            model.print_model();
            model.vars().filter(|l| l.is_pos()).count() <= k as usize
        });
        assert_eq!(
            res.correct as u32,
            (0..=k).map(|i| binomial(range, i)).sum()
        );
        assert_eq!(res.total(), 1 << range);
    }

    #[test]
    fn normal_atleastk() {
        let mut encoder = DefaultEncoder::new();

        let range = 10;
        let k = 5;
        let lits = (0..range).map(|i| Pos(i));

        encoder.add_constraint(AtleastK { k, lits });

        let res = retry_until_unsat(&mut encoder, |model| {
            //model.print_model();
            let mut v: Vec<_> = model.vars().collect();
            v.sort();
            println!("{:?}", v);
            assert!(model.vars().filter(|l| l.is_pos()).count() >= k as usize)
        });
        assert_eq!(res as u32, (k..=range).map(|i| binomial(range, i)).sum());
    }

    #[test]
    fn normal_atleast0() {
        let mut encoder = DefaultEncoder::new();

        let range = 5;
        let k = 0;
        let lits = (0..range).map(Pos);

        // Because atleast 0 shouldn't encode anything we add an equivalent var for
        // each var so every var appears in the resulting set of clauses.
        // Otherwise the sat solver has no variables and just returns an empty set as
        // the only solution.
        for (l1, l2) in lits.clone().zip((range..2 * range).map(Pos)) {
            encoder.add_constraint(Equal(vec![l1, l2].into_iter()));
        }

        encoder.add_constraint(AtleastK { k, lits });

        let res = retry_until_unsat(&mut encoder, |model| {
            //model.print_model();
            let mut v: Vec<_> = model.vars().collect();
            v.sort();
            println!("{:?}", v);
            assert!(model.vars().filter(|l| l.is_pos()).count() >= k as usize)
        });
        assert_eq!(res as u32, 1 << range);
    }

    #[test]
    fn atleastk_implies_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 10;
        let k = 6;
        let lits = (1..=range).map(|i| Pos(i));
        let constraint = AtleastK { k, lits };

        let repr = constraint.encode_constraint_implies_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );
        assert!(repr > 0);

        let res = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            model.vars().filter(|l| l.is_pos()).count() >= k as usize
        });
        assert_eq!(
            res.correct as u32,
            (k..=range).map(|i| binomial(range, i)).sum()
        );
        assert_eq!(res.total(), 1 << range);
    }

    #[test]
    fn atleastk_equals_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 10;
        let k = 5;
        let lits = (1..=range).map(|i| Pos(i));
        let constraint = AtleastK { k, lits };

        let repr = constraint.encode_constraint_equals_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );
        assert!(repr > 0);

        let res = constraint_equals_repr_tester(&mut encoder, repr, |model| {
            model.vars().filter(|l| l.is_pos()).count() >= k as usize
        });
        assert_eq!(
            res.correct as u32,
            (k..=range).map(|i| binomial(range, i)).sum()
        );
        assert_eq!(res.total(), 1 << range);
    }

    #[test]
    fn atleast0_implies_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 10;
        let k = 0;
        let lits = (1..=range).map(|i| Pos(i));

        for (l1, l2) in lits.clone().zip(((range + 1)..=(2 * range)).map(Pos)) {
            encoder.add_constraint(Equal(vec![l1, l2].into_iter()));
        }

        let constraint = AtleastK { k, lits };

        let repr = encoder.varmap.new_var();
        constraint.encode_constraint_implies_repr(
            Some(repr),
            &mut encoder.solver,
            &mut encoder.varmap,
        );

        let res = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            model.vars().filter(|l| l.is_pos()).count() >= k as usize
        });
        assert_eq!(res.correct, 1 << range);
        assert_eq!(res.total(), 1 << range);
    }

    #[test]
    fn atleast0_equals_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 10;
        let k = 0;
        let lits = (1..=range).map(|i| Pos(i));

        for (l1, l2) in lits.clone().zip(((range + 1)..=(2 * range)).map(Pos)) {
            encoder.add_constraint(Equal(vec![l1, l2].into_iter()));
        }

        let constraint = AtleastK { k, lits };

        let repr = constraint.encode_constraint_equals_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );
        assert_ne!(repr, 0);

        let res = constraint_equals_repr_tester(&mut encoder, repr, |model| {
            model.vars().filter(|l| l.is_pos()).count() >= k as usize
        });
        assert_eq!(
            res.correct as u32,
            (k..=range).map(|i| binomial(range, i)).sum()
        );
        assert_eq!(res.total(), 1 << range);
    }

    #[test]
    fn normal_exactlyk() {
        let mut encoder = DefaultEncoder::new();

        let range = 10;
        let k = 5;
        let lits = (0..range).map(|i| Pos(i));

        encoder.add_constraint(ExactlyK { k, lits });

        let res = retry_until_unsat(&mut encoder, |model| {
            model.print_model();
            assert!(model.vars().filter(|l| l.is_pos()).count() == k as usize)
        });
        assert_eq!(res as u32, binomial(range, k));
    }

    #[test]
    fn normal_exactly0() {
        let mut encoder = DefaultEncoder::new();

        let range = 5;
        let k = 0;
        let lits = (0..range).map(Pos);

        for (l1, l2) in lits.clone().zip((range..2 * range).map(Pos)) {
            encoder.add_constraint(Equal(vec![l1, l2].into_iter()));
        }

        encoder.add_constraint(ExactlyK { k, lits });

        let res = retry_until_unsat(&mut encoder, |model| {
            model.print_model();
            assert!(model.vars().filter(|l| l.is_pos()).count() == k as usize)
        });
        assert_eq!(res as u32, 1);
    }

    #[test]
    fn exactlyk_implies_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 10;
        let k = 6;
        let lits = (1..=range).map(|i| Pos(i));
        let constraint = ExactlyK { k, lits };

        let repr = constraint.encode_constraint_implies_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );
        assert!(repr > 0);

        let res = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            model.vars().filter(|l| l.is_pos()).count() == k as usize
        });
        assert_eq!(res.correct as u32, binomial(range, k));
        assert_eq!(res.total(), 1 << range);
    }

    #[test]
    fn exactlyk_equals_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 10;
        let k = 5;
        let lits = (1..=range).map(|i| Pos(i));
        let constraint = ExactlyK { k, lits };

        let repr = constraint.encode_constraint_equals_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );
        assert!(repr > 0);

        let res = constraint_equals_repr_tester(&mut encoder, repr, |model| {
            model.vars().filter(|l| l.is_pos()).count() == k as usize
        });
        assert_eq!(res.correct as u32, binomial(range, k));
        assert_eq!(res.total(), 1 << range);
    }

    #[test]
    fn exactly0_implies_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 10;
        let k = 0;
        let lits = (1..=range).map(|i| Pos(i));

        for (l1, l2) in lits.clone().zip(((range + 1)..=(2 * range)).map(Pos)) {
            encoder.add_constraint(Equal(vec![l1, l2].into_iter()));
        }

        let constraint = ExactlyK { k, lits };

        let repr = encoder.varmap.new_var();
        constraint.encode_constraint_implies_repr(
            Some(repr),
            &mut encoder.solver,
            &mut encoder.varmap,
        );

        let res = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            model.vars().filter(|l| l.is_pos()).count() == k as usize
        });
        assert_eq!(res.correct, 1);
        assert_eq!(res.total(), 1 << range);
    }

    #[test]
    fn exactly0_equals_repr() {
        let mut encoder = DefaultEncoder::new();

        let range = 10;
        let k = 0;
        let lits = (1..=range).map(|i| Pos(i));

        for (l1, l2) in lits.clone().zip(((range + 1)..=(2 * range)).map(Pos)) {
            encoder.add_constraint(Equal(vec![l1, l2].into_iter()));
        }

        let constraint = ExactlyK { k, lits };

        let repr = constraint.encode_constraint_equals_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );
        assert_ne!(repr, 0);

        let res = constraint_equals_repr_tester(&mut encoder, repr, |model| {
            model.vars().filter(|l| l.is_pos()).count() == k as usize
        });
        assert_eq!(res.correct as u32, 1);
        assert_eq!(res.total(), 1 << range);
    }
}
