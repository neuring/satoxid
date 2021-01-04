use core::fmt;
use std::{fmt::Debug, iter::once};

use crate::circuit::{Circuit, Direction};
use crate::{
    clause, Constraint, ConstraintRepr, Encoder, Lit, SatVar, Solver, VarMap,
};

enum EncodeConfig {
    Normal,
    ImplRepr(i32),
    EqualRepr(i32),
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
        encode_atmost_k(self, EncodeConfig::Normal, solver, varmap);
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
        let repr = repr.unwrap_or_else(|| varmap.new_var());
        // Generate repr for `encode_atmost_k`.
        encode_atmost_k(self, EncodeConfig::ImplRepr(repr), solver, varmap);
        repr
    }

    fn encode_constraint_equals_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| varmap.new_var());
        encode_atmost_k(self, EncodeConfig::EqualRepr(repr), solver, varmap);
        repr
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

/// Encoding AtMostK constraint using Sequential Counter.
fn encode_atmost_k<V, S, I>(
    constraint: AtMostK<I>,
    config: EncodeConfig,
    solver: &mut S,
    varmap: &mut VarMap<V>,
) where
    V: SatVar,
    S: Solver,
    I: Iterator<Item = Lit<V>>,
{
    use EncodeConfig::*;

    let dir = match config {
        Normal => Direction::InToOut,
        ImplRepr(_) => Direction::Both,
        EqualRepr(_) => Direction::Both,
    };

    let mut circuit = Circuit::new(solver, dir);

    if constraint.k == 0 {
        if let ImplRepr(repr) = config {
            let lits = constraint.lits.map(|lit| varmap.add_var(lit));
            circuit.solver.add_clause(lits.chain(clause![repr]));
        } else {
            for v in constraint.lits {
                let v = varmap.add_var(v);
                circuit.set_zero(v);
            }
        }

        return;
    }

    let vars: Vec<_> = constraint.lits.map(|v| varmap.add_var(v)).collect();
    let n = vars.len();
    let k = constraint.k as usize;

    let mut prev_s: Vec<_> = (0..k).map(|_| varmap.new_var()).collect();

    if let Some(&v) = vars.first() {
        circuit.equal(v, prev_s[0]);
    } else {
        return;
    }

    for &s in prev_s.iter().skip(1) {
        circuit.set_zero(s);
    }

    let mut endings_repr = Vec::new();
    for (i, &v) in vars.iter().enumerate().skip(1) {
        if i + 1 == n {
            if matches!(config, ImplRepr(_) | EqualRepr(_)) {
                let e_repr = varmap.new_var();

                circuit.and_gate(clause![v, prev_s[k - 1]], e_repr);

                endings_repr.push(e_repr);
            } else {
                circuit.solver.add_clause(clause!(-v, -prev_s[k - 1]));
            }
            break;
        }

        let new_s: Vec<_> = (0..k).map(|_| varmap.new_var()).collect();

        circuit.or_gate(clause![v, prev_s[0]], new_s[0]);

        for j in 1usize..(k as usize) {
            let a = varmap.new_var();

            circuit.and_gate(clause![v, prev_s[j - 1]], a);
            circuit.or_gate(clause![a, prev_s[j]], new_s[j]);
        }

        if matches!(config, ImplRepr(_) | EqualRepr(_)) {
            let e_repr = varmap.new_var();
            circuit.and_gate(clause![v, prev_s[k - 1]], e_repr);
            endings_repr.push(e_repr);
        } else {
            circuit.solver.add_clause(clause!(-v, -prev_s[k - 1]));
        }
        prev_s = new_s;
    }

    if let ImplRepr(repr) = config {
        circuit
            .solver
            .add_clause(endings_repr.iter().copied().chain(clause![repr]));
    } else if let EqualRepr(repr) = config {
        circuit
            .solver
            .add_clause(endings_repr.iter().copied().chain(clause![repr]));
        for e_repr in endings_repr {
            circuit.solver.add_clause(clause![-repr, -e_repr]);
        }
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
        encode_atleast_k(self, EncodeConfig::Normal, solver, varmap);
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
        let repr = repr.unwrap_or_else(|| varmap.new_var());

        encode_atleast_k(self, EncodeConfig::ImplRepr(repr), solver, varmap);

        repr
    }

    fn encode_constraint_equals_repr<S: Solver>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        let repr = repr.unwrap_or_else(|| varmap.new_var());

        encode_atleast_k(self, EncodeConfig::EqualRepr(repr), solver, varmap);

        repr
    }
}

/// Encoding AtleastK constraint using Sequential Counter.
fn encode_atleast_k<V, S, I>(
    constraint: AtleastK<I>,
    config: EncodeConfig,
    solver: &mut S,
    varmap: &mut VarMap<V>,
) where
    V: SatVar,
    S: Solver,
    I: Iterator<Item = Lit<V>>,
{
    use EncodeConfig::*;

    if constraint.k == 0 {
        match config {
            Normal => {},
            EqualRepr(repr) | ImplRepr(repr) => solver.add_clause(clause![repr]),
        }
        return;
    }

    let dir = match config {
        Normal => Direction::OutToIn,
        ImplRepr(_) => Direction::InToOut,
        EqualRepr(_) => Direction::Both,
    };

    let mut circuit = Circuit::new(solver, dir);

    let vars: Vec<_> = constraint.lits.map(|v| varmap.add_var(v)).collect();
    println!("vars = {:?}", vars);
    let n = vars.len();
    let k = constraint.k as usize;

    let mut prev_s: Vec<_> = (0..k).map(|_| varmap.new_var()).collect();

    if let Some(&v) = vars.first() {
        circuit.equal(v, prev_s[0]);
    } else {
        return;
    }

    for &s in prev_s.iter().skip(1) {
        circuit.set_zero(s);
    }

    for (i, &v) in vars.iter().enumerate().skip(1) {
        let new_s: Vec<_> = (0..k).map(|_| varmap.new_var()).collect();

        circuit.or_gate(clause![v, prev_s[0]], new_s[0]);

        for j in 1usize..(k as usize) {
            let a = varmap.new_var();

            circuit.and_gate(clause![v, prev_s[j - 1]], a);
            circuit.or_gate(clause![a, prev_s[j]], new_s[j]);
        }

        prev_s = new_s;
    }

    match config {
        EncodeConfig::Normal => circuit.solver.add_clause(clause!(prev_s[k - 1])),
        EncodeConfig::ImplRepr(repr) => {
            circuit.solver.add_clause(clause![-prev_s[k - 1], repr])
        }
        EncodeConfig::EqualRepr(repr) => {
            circuit.solver.add_clause(clause![-prev_s[k - 1], repr]);
            circuit.solver.add_clause(clause![prev_s[k - 1], -repr]);
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

/// Constraints all elements of `lits` to contain exactly k true variables.
#[derive(Clone)]
struct ExactlyK<I> {
    lits: I,
    k: u32,
}

impl<V: Debug, I> Debug for ExactlyK<I>
where
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<_> = self.lits.clone().collect();

        f.debug_struct("ExactlyK")
            .field("k", &self.k)
            .field("lits", &lits)
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
            Clause,
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
        assert!(repr > 0);

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
            encoder.add_constraint(Clause(vec![l1, !l2].into_iter()));
            encoder.add_constraint(Clause(vec![!l1, l2].into_iter()));
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
            encoder.add_constraint(Clause(vec![l1, !l2].into_iter()));
            encoder.add_constraint(Clause(vec![!l1, l2].into_iter()));
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
}
