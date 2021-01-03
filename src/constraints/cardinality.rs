use core::fmt;
use std::{fmt::Debug, iter::once};

use crate::{clause, Constraint, ConstraintRepr, Encoder, Lit, SatVar, Solver, VarMap};

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
        encode_atmost_k(self, None, solver, varmap);
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
        encode_atmost_k(self, Some(repr), solver, varmap);
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
/// If no repr is required only direction suffices.
/// If a repr is required all circuits need to be defined both ways.
/// The `repr` argument here has different meaning than the one in the `ConstraintRepr`
/// trait. Here it means whether the encoding should be generated with a repr or without.
/// Unlike the trait where it means that a new repr should be generated.
fn encode_atmost_k<V, S, I>(
    constraint: AtMostK<I>,
    repr: Option<i32>,
    solver: &mut S,
    varmap: &mut VarMap<V>,
) where
    V: SatVar,
    S: Solver,
    I: Iterator<Item = Lit<V>>,
{
    use crate::circuit::{Circuit, Direction};

    let dir = if let Some(_) = repr {
        Direction::Both
    } else {
        Direction::InToOut
    };

    let mut circuit = Circuit::new(solver, dir);

    if constraint.k == 0 {
        if let Some(repr) = repr {
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
            if let Some(_) = repr {
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

        if let Some(_) = repr {
            let e_repr = varmap.new_var();
            circuit.and_gate(clause![v, prev_s[k - 1]], e_repr);
            endings_repr.push(e_repr);
        } else {
            circuit.solver.add_clause(clause!(-v, -prev_s[k - 1]));
        }
        prev_s = new_s;
    }

    if let Some(repr) = repr {
        circuit
            .solver
            .add_clause(endings_repr.iter().copied().chain(clause![repr]));
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
    V: SatVar + Debug + Clone,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode<S: Solver>(self, solver: &mut S, varmap: &mut VarMap<V>) {
        let k = self.k as usize;

        let vars: Vec<_> = self.lits.map(|v| varmap.add_var(v)).collect();

        if k == 0 {
            return;
        } else if k == 1 {
            solver.add_clause(vars.into_iter());
            return;
        }

        let n = vars.len();

        let mut prev_s: Vec<_> = (0..k).map(|_| varmap.new_var()).collect();

        solver.add_clause(clause!(vars[0], prev_s[k - 1]));
        solver.add_clause(clause!(prev_s[k - 1], prev_s[k - 2]));

        for (i, &v) in vars.iter().enumerate().skip(1) {
            if i + 1 == n {
                solver.add_clause(clause!(-prev_s[0], v));
                for j in 1..k {
                    solver.add_clause(clause!(-prev_s[j]));
                }

                break;
            }

            let mut new_s: Vec<_> = (0..k).map(|_| varmap.new_var()).collect();

            solver.add_clause(clause!(-prev_s[0], new_s[0], v));

            for j in 1..k {
                solver.add_clause(clause!(-prev_s[j], new_s[j], v));
                solver.add_clause(clause!(-prev_s[j], new_s[j], new_s[j - 1]));
            }

            std::mem::swap(&mut prev_s, &mut new_s);
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
        constraints::test_util::{
            constraint_equals_repr_tester, constraint_implies_repr_tester, retry_until_unsat,
        },
        prelude::*,
        Solver, VarType,
    };

    use super::*;

    #[test]
    fn normal_atmostk() {
        let mut encoder = Encoder::<_, cadical::Solver>::new();

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
        let mut encoder = Encoder::<_, cadical::Solver>::new();

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
        let mut encoder = Encoder::<_, cadical::Solver>::new();

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
        assert_eq!(res.correct as u32, (0..=k).map(|i| binomial(range, i)).sum());
        assert_eq!(res.total(), 1 << range);
    }

    #[test]
    fn atmostk_equals_repr() {
        let mut encoder = Encoder::<_, cadical::Solver>::new();

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
        assert_eq!(res.correct as u32, (0..=k).map(|i| binomial(range, i)).sum());
        assert_eq!(res.total(), 1 << range);
    }

    #[test]
    fn atmost0_implies_repr() {
        let mut encoder = Encoder::<_, cadical::Solver>::new();

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
    fn atleastk() {
        let mut encoder = Encoder::<_, cadical::Solver>::new();

        let range = 10;
        let k = 5;
        let lits = (0..range).map(|i| Pos(i));

        encoder.add_constraint(AtleastK { k, lits });

        let res = retry_until_unsat(&mut encoder, |model| {
            assert!(model.vars().filter(|l| l.is_pos()).count() >= k as usize)
        });
        assert_eq!(res as u32, (k..=range).map(|i| binomial(range, i)).sum());
    }
}
