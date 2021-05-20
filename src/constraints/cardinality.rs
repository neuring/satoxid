use core::fmt;
use std::{fmt::Debug, iter};

use crate::{
    circuit::{Circuit, Direction},
    clause, Backend, Constraint, ConstraintRepr, SatVar, VarMap, VarType,
};

/// Encodes a sequential counter used for all cardinality constraint types.
/// Returns the k output vars which different constraints can constrain to
/// achieve their respective behaviour.
fn encode_cardinality_constraint<V, S, L, I>(
    lits: I,
    k: u32,
    dir: Direction,
    out: Option<&[i32]>,
    solver: &mut S,
    varmap: &mut VarMap<V>,
) -> Vec<i32>
where
    V: SatVar,
    S: Backend,
    I: Iterator<Item = L>,
    L: Into<VarType<V>>,
{
    assert!(k > 0);
    if let Some(out) = out {
        assert!(k as usize <= out.len());
    }

    let mut circuit = Circuit::new(solver, dir);

    let vars: Vec<_> = lits.map(|v| varmap.add_var(v)).collect();

    if k == 1 {
        return if let Some(out) = out {
            circuit.or_gate(vars.into_iter(), out[0]);

            for &o in out.iter().skip(1) {
                circuit.solver.add_clause(clause!(-o));
            }

            vec![out[0]]
        } else {
            let out = varmap.new_var();
            circuit.or_gate(vars.into_iter(), out);
            vec![out]
        };
    }

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
        let new_s: Vec<_> = if i + 1 == vars.len() && out.is_some() {
            out.unwrap().to_owned()
        } else {
            (0..k).map(|_| varmap.new_var()).collect()
        };

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

impl<V, L, I> Constraint<V> for AtMostK<I>
where
    V: SatVar,
    L: Into<VarType<V>> + Debug,
    I: Iterator<Item = L> + Clone,
{
    fn encode<S: Backend>(self, solver: &mut S, varmap: &mut VarMap<V>) {
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
                None,
                solver,
                varmap,
            );

            solver.add_clause(clause![-out.last().unwrap()]);
        }
    }
}

impl<V, L, I> ConstraintRepr<V> for AtMostK<I>
where
    V: SatVar,
    L: Into<VarType<V>> + Debug,
    I: Iterator<Item = L> + Clone,
{
    fn encode_constraint_implies_repr<S: Backend>(
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
                None,
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

    fn encode_constraint_equals_repr<S: Backend>(
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
                None,
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

impl<L: Debug, I> Debug for AtMostK<I>
where
    L: Debug,
    I: Iterator<Item = L> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<_> = self.lits.clone().collect();

        f.debug_struct("AtMostK")
            .field("k", &self.k)
            .field("vars", &lits)
            .finish()
    }
}

/// This constraint encodes the requirement that at least `k` of `lits` variables
/// are true.
#[derive(Clone)]
pub struct AtLeastK<I> {
    pub lits: I,
    pub k: u32,
}

impl<V, L, I> Constraint<V> for AtLeastK<I>
where
    V: SatVar,
    L: Into<VarType<V>> + Debug,
    I: Iterator<Item = L> + Clone,
{
    fn encode<S: Backend>(self, solver: &mut S, varmap: &mut VarMap<V>) {
        if self.k == 0 {
            return;
        } else {
            let out = encode_cardinality_constraint(
                self.lits,
                self.k,
                Direction::OutToIn,
                None,
                solver,
                varmap,
            );

            solver.add_clause(clause![*out.last().unwrap()]);
        }
    }
}

impl<V, L, I> ConstraintRepr<V> for AtLeastK<I>
where
    V: SatVar,
    L: Into<VarType<V>> + Debug,
    I: Iterator<Item = L> + Clone,
{
    fn encode_constraint_implies_repr<S: Backend>(
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
                None,
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

    fn encode_constraint_equals_repr<S: Backend>(
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
                None,
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

impl<V: Debug, I> Debug for AtLeastK<I>
where
    I: Iterator<Item = V> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<_> = self.lits.clone().collect();

        f.debug_struct("AtLeastK")
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

impl<V, L, I> Constraint<V> for ExactlyK<I>
where
    V: SatVar,
    L: Into<VarType<V>> + Debug,
    I: Iterator<Item = L> + Clone,
{
    fn encode<S: Backend>(self, solver: &mut S, varmap: &mut VarMap<V>) {
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
                None,
                solver,
                varmap,
            );

            solver.add_clause(clause![out[out.len() - 2]]);
            solver.add_clause(clause![-out[out.len() - 1]]);
        }
    }
}

impl<V, L, I> ConstraintRepr<V> for ExactlyK<I>
where
    V: SatVar,
    L: Into<VarType<V>> + Debug,
    I: Iterator<Item = L> + Clone,
{
    fn encode_constraint_implies_repr<S: Backend>(
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
                None,
                solver,
                varmap,
            );

            let r1 = out[out.len() - 2];
            let r2 = out[out.len() - 1];

            solver.add_clause(clause!(-r1, r2, repr));
        }

        repr
    }

    fn encode_constraint_equals_repr<S: Backend>(
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
                None,
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

impl<L: Debug, I> Debug for ExactlyK<I>
where
    I: Iterator<Item = L> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<_> = self.lits.clone().collect();

        f.debug_struct("ExactlyK")
            .field("k", &self.k)
            .field("vars", &lits)
            .finish()
    }
}

/// Constraint to ensure that several sets of literals have each the same number of true
/// values.
#[derive(Clone, Debug)]
pub struct SameCardinality<V> {
    lits: Vec<Vec<VarType<V>>>,
}

impl<V> SameCardinality<V> {
    pub fn new() -> Self {
        Self { lits: Vec::new() }
    }

    pub fn add_lits<I, L>(&mut self, lits: I) -> &mut Self
    where
        L: Into<VarType<V>>,
        I: Iterator<Item = L>,
    {
        self.lits.push(lits.map(|l| l.into()).collect());
        self
    }
}

impl<V: SatVar> Constraint<V> for SameCardinality<V> {
    fn encode<S: Backend>(self, solver: &mut S, varmap: &mut VarMap<V>) {
        if self.lits.is_empty() {
            return;
        }

        let max = self.lits.iter().map(|l| l.len()).max().unwrap();
        let min = self.lits.iter().map(|l| l.len()).min().unwrap();

        let repr: Vec<_> = (0..max).map(|_| varmap.new_var()).collect();

        for v in repr.iter().rev().take(max - min) {
            solver.add_clause(clause![-v]);
        }

        for lits in self.lits {
            let k = lits.len();
            encode_cardinality_constraint(
                lits.into_iter(),
                k as u32,
                Direction::Both,
                Some(&repr),
                solver,
                varmap,
            );
        }
    }
}

impl<V: SatVar> ConstraintRepr<V> for SameCardinality<V> {
    fn encode_constraint_implies_repr<S: Backend>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        encode_same_cardinality_repr(self, repr, solver, varmap, false)
    }

    fn encode_constraint_equals_repr<S: Backend>(
        self,
        repr: Option<i32>,
        solver: &mut S,
        varmap: &mut VarMap<V>,
    ) -> i32 {
        encode_same_cardinality_repr(self, repr, solver, varmap, true)
    }
}

fn encode_same_cardinality_repr<V: SatVar>(
    constraint: SameCardinality<V>,
    repr: Option<i32>,
    solver: &mut impl Backend,
    varmap: &mut VarMap<V>,
    equal: bool,
) -> i32 {
    let repr = repr.unwrap_or_else(|| varmap.new_var());

    if constraint.lits.is_empty() {
        solver.add_clause(clause!(repr));
        return repr;
    }

    let max = constraint.lits.iter().map(|l| l.len()).max().unwrap();

    let mut reprs = Vec::new();

    for lits in constraint.lits {
        let repr: Vec<_> = (0..max).map(|_| varmap.new_var()).collect();

        let k = lits.len();

        for v in repr.iter().rev().take(max - k) {
            solver.add_clause(clause![-v]);
        }

        encode_cardinality_constraint(
            lits.into_iter(),
            k as u32,
            Direction::Both,
            Some(&repr),
            solver,
            varmap,
        );

        reprs.push(repr);
    }

    let mut equiv_reprs = Vec::new();
    for i in 0..max {
        let r = varmap.new_var();

        solver.add_clause(reprs.iter().map(|repr| repr[i]).chain(clause![r]));
        solver.add_clause(reprs.iter().map(|repr| -repr[i]).chain(clause![r]));

        if equal {
            for repr_window in reprs.windows(2) {
                solver.add_clause(clause![
                    -repr_window[0][i],
                    repr_window[1][i],
                    -r
                ]);
            }
            solver.add_clause(clause![-reprs[reprs.len() - 1][i], reprs[0][i], -r]);
        }

        equiv_reprs.push(r);
    }

    if equal {
        for &equiv_repr in &equiv_reprs {
            solver.add_clause(clause!(-repr, equiv_repr));
        }
    }
    solver.add_clause(equiv_reprs.into_iter().map(|l| -l).chain(clause![repr]));

    repr
}

#[derive(Clone)]
pub struct LessCardinality<I1, I2> {
    larger: I1,
    smaller: I2,
}

impl<I1, I2, L1, L2, V> Constraint<V> for LessCardinality<I1, I2>
where
    V: SatVar,
    L1: Into<VarType<V>> + Debug,
    L2: Into<VarType<V>> + Debug,
    I1: Iterator<Item = L1> + Clone,
    I2: Iterator<Item = L2> + Clone,
{
    fn encode<S: Backend>(self, solver: &mut S, varmap: &mut VarMap<V>) {
        let larger = self.larger.collect::<Vec<_>>();
        let larger_len = larger.len();

        let smaller = self.smaller.collect::<Vec<_>>();
        let smaller_len = smaller.len();

        let max = usize::max(larger_len, smaller_len);

        let mut larger_out = encode_cardinality_constraint(
            larger.into_iter(),
            larger_len as u32,
            Direction::OutToIn,
            None,
            solver,
            varmap,
        );

        let mut smaller_out = encode_cardinality_constraint(
            smaller.into_iter(),
            smaller_len as u32,
            Direction::InToOut,
            None,
            solver,
            varmap,
        );

        larger_out
            .extend(iter::from_fn(|| Some(varmap.new_var())).take(max - larger_len));
        smaller_out.extend(
            iter::from_fn(|| Some(varmap.new_var())).take(max - smaller_len),
        );

        for i in 1..max {
            solver.add_clause(clause!(
                -smaller_out[i - 1],
                smaller_out[i],
                larger_out[i]
            ));
        }

        solver.add_clause(clause!(*larger_out.first().unwrap()));
        solver.add_clause(clause!(-*smaller_out.last().unwrap()));
    }
}

//impl<V: SatVar> ConstraintRepr<V> for LessCardinality<V> {
//    fn encode_constraint_implies_repr<S: Solver>(
//        self,
//        repr: Option<i32>,
//        solver: &mut S,
//        varmap: &mut VarMap<V>,
//    ) -> i32 {
//        todo!()
//    }
//}

impl<L1, L2, I1, I2> Debug for LessCardinality<I1, I2>
where
    L1: Debug,
    L2: Debug,
    I1: Iterator<Item = L1> + Clone,
    I2: Iterator<Item = L2> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let larger: Vec<_> = self.larger.clone().collect();
        let smaller: Vec<_> = self.smaller.clone().collect();

        f.debug_struct("LessCardinality")
            .field("larger", &larger)
            .field("smaller", &smaller)
            .finish()
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
            Equal,
        },
        CadicalEncoder,
        Lit::*,
    };

    #[test]
    fn normal_atmostk() {
        let mut encoder = CadicalEncoder::new();

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
        let mut encoder = CadicalEncoder::new();

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
    fn normal_atmost_one_literal() {
        let mut encoder = CadicalEncoder::new();

        let lits = std::iter::once(Pos(1));
        let k = 1;

        encoder.add_constraint(AtMostK { k, lits });

        let models = retry_until_unsat(&mut encoder, |model| {
            model.print_model();
        });
        assert_eq!(models, 2);
    }

    #[test]
    fn atmostk_implies_repr() {
        let mut encoder = CadicalEncoder::new();

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
        let mut encoder = CadicalEncoder::new();

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
        let mut encoder = CadicalEncoder::new();

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
        let mut encoder = CadicalEncoder::new();

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
    fn normal_at_least_k() {
        let mut encoder = CadicalEncoder::new();

        let range = 10;
        let k = 5;
        let lits = (0..range).map(|i| Pos(i));

        encoder.add_constraint(AtLeastK { k, lits });

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
    fn normal_at_least_one_literal() {
        let mut encoder = CadicalEncoder::new();

        let k = 1;
        let lits = std::iter::once(Pos(1));

        encoder.add_constraint(AtLeastK { k, lits });

        let res =
            retry_until_unsat(&mut encoder, |model| assert!(model.var(1).unwrap()));
        assert_eq!(res, 1);
    }

    #[test]
    fn normal_at_least_0() {
        let mut encoder = CadicalEncoder::new();

        let range = 5;
        let k = 0;
        let lits = (0..range).map(Pos);

        // Because AtLeast 0 shouldn't encode anything we add an equivalent var for
        // each var so every var appears in the resulting set of clauses.
        // Otherwise the sat solver has no variables and just returns an empty set as
        // the only solution.
        for (l1, l2) in lits.clone().zip((range..2 * range).map(Pos)) {
            encoder.add_constraint(Equal(vec![l1, l2].into_iter()));
        }

        encoder.add_constraint(AtLeastK { k, lits });

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
    fn normal_at_least_1() {
        let mut encoder = CadicalEncoder::new();

        let range = 5;
        let k = 1;
        let lits = (0..range).map(Pos);

        encoder.add_constraint(AtLeastK { k, lits });

        let res = retry_until_unsat(&mut encoder, |model| {
            model.print_model();
            assert!(model.vars().filter(|l| l.is_pos()).count() >= k as usize)
        });
        assert_eq!(res as u32, (1 << range) - 1);
    }

    #[test]
    fn at_least_k_implies_repr() {
        let mut encoder = CadicalEncoder::new();

        let range = 10;
        let k = 6;
        let lits = (1..=range).map(|i| Pos(i));
        let constraint = AtLeastK { k, lits };

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
    fn at_least_k_equals_repr() {
        let mut encoder = CadicalEncoder::new();

        let range = 10;
        let k = 5;
        let lits = (1..=range).map(|i| Pos(i));
        let constraint = AtLeastK { k, lits };

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
    fn at_least_0_implies_repr() {
        let mut encoder = CadicalEncoder::new();

        let range = 10;
        let k = 0;
        let lits = (1..=range).map(|i| Pos(i));

        for (l1, l2) in lits.clone().zip(((range + 1)..=(2 * range)).map(Pos)) {
            encoder.add_constraint(Equal(vec![l1, l2].into_iter()));
        }

        let constraint = AtLeastK { k, lits };

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
    fn at_least_0_equals_repr() {
        let mut encoder = CadicalEncoder::new();

        let range = 10;
        let k = 0;
        let lits = (1..=range).map(|i| Pos(i));

        for (l1, l2) in lits.clone().zip(((range + 1)..=(2 * range)).map(Pos)) {
            encoder.add_constraint(Equal(vec![l1, l2].into_iter()));
        }

        let constraint = AtLeastK { k, lits };

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
        let mut encoder = CadicalEncoder::new();

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
        let mut encoder = CadicalEncoder::new();

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
        let mut encoder = CadicalEncoder::new();

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
        let mut encoder = CadicalEncoder::new();

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
        let mut encoder = CadicalEncoder::new();

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
        let mut encoder = CadicalEncoder::new();

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

    #[test]
    fn normal_same_cardinality() {
        let mut encoder = CadicalEncoder::new();

        let range: u32 = 5;

        let mut constraint = SameCardinality::new();
        constraint
            .add_lits((0..range).map(Pos))
            .add_lits((range..2 * range).map(Pos));

        encoder.add_constraint(constraint);

        let res = retry_until_unsat(&mut encoder, |model| {
            model.print_model();
            let c1 = model
                .vars()
                .filter(|l| (0..range).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            let c2 = model
                .vars()
                .filter(|l| (range..2 * range).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            assert_eq!(c1, c2);
        });

        assert_eq!(
            res as u32,
            (0..=range).map(|i| binomial(range, i).pow(2)).sum::<u32>()
        );
    }

    #[test]
    fn normal_same_cardinality_one_large_size() {
        let mut encoder = CadicalEncoder::new();

        let range1: u32 = 1;
        let range2: u32 = 5;

        let mut constraint = SameCardinality::new();
        constraint
            .add_lits((0..range1).map(Pos))
            .add_lits((range1..range1 + range2).map(Pos));

        encoder.add_constraint(constraint);

        let res = retry_until_unsat(&mut encoder, |model| {
            model.print_model();
            let c1 = model
                .vars()
                .filter(|l| (0..range1).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            let c2 = model
                .vars()
                .filter(|l| (range1..range1 + range2).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            assert_eq!(c1, c2);
        });

        assert_eq!(res as u32, 6,);
    }

    #[test]
    fn normal_same_cardinality_different_sizes() {
        let mut encoder = CadicalEncoder::new();

        let range1: u32 = 3;
        let range2: u32 = 5;

        let mut constraint = SameCardinality::new();
        constraint
            .add_lits((0..range1).map(Pos))
            .add_lits((range1..range1 + range2).map(Pos));

        encoder.add_constraint(constraint);

        let res = retry_until_unsat(&mut encoder, |model| {
            model.print_model();
            let c1 = model
                .vars()
                .filter(|l| (0..range1).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            let c2 = model
                .vars()
                .filter(|l| (range1..range1 + range2).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            assert_eq!(c1, c2);
        });

        assert_eq!(
            res as u32,
            (0..=range1)
                .map(|i| binomial(range1, i) * binomial(range2, i))
                .sum::<u32>()
        );
    }

    #[test]
    fn normal_same_cardinality_but_more() {
        let mut encoder = CadicalEncoder::new();

        let range: u32 = 3;

        let mut constraint = SameCardinality::new();
        constraint
            .add_lits((0..range).map(Pos))
            .add_lits((range..2 * range).map(Pos))
            .add_lits((2 * range..3 * range).map(Pos))
            .add_lits((3 * range..4 * range).map(Pos));

        encoder.add_constraint(constraint);

        let res = retry_until_unsat(&mut encoder, |model| {
            model.print_model();
            let c1 = model
                .vars()
                .filter(|l| (0..range).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            let c2 = model
                .vars()
                .filter(|l| (range..2 * range).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            let c3 = model
                .vars()
                .filter(|l| (2 * range..3 * range).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            let c4 = model
                .vars()
                .filter(|l| (3 * range..4 * range).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            assert_eq!(c1, c2);
            assert_eq!(c1, c3);
            assert_eq!(c1, c4);
        });

        assert_eq!(
            res as u32,
            (0..=range).map(|i| binomial(range, i).pow(4)).sum::<u32>()
        );
    }

    #[test]
    fn same_cardinality_implies_repr() {
        let mut encoder = CadicalEncoder::new();

        let range: u32 = 5;

        let mut constraint = SameCardinality::new();
        constraint
            .add_lits((0..range).map(Pos))
            .add_lits((range..2 * range).map(Pos));

        let repr = constraint.encode_constraint_implies_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );

        let res = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            let c1 = model
                .vars()
                .filter(|l| (0..range).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            let c2 = model
                .vars()
                .filter(|l| (range..2 * range).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            c1 == c2
        });

        assert_eq!(
            res.correct as u32,
            (0..=range).map(|i| binomial(range, i).pow(2)).sum::<u32>()
        );
        assert_eq!(res.total(), 1 << (2 * range));
    }

    #[test]
    fn same_cardinality_implies_repr_different_sizes() {
        let mut encoder = CadicalEncoder::new();

        let range1: u32 = 5;
        let range2: u32 = 3;

        let mut constraint = SameCardinality::new();
        constraint
            .add_lits((0..range1).map(Pos))
            .add_lits((range1..range1 + range2).map(Pos));

        let repr = constraint.encode_constraint_implies_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );

        let res = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            let c1 = model
                .vars()
                .filter(|l| (0..range1).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            let c2 = model
                .vars()
                .filter(|l| (range1..range1 + range2).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            c1 == c2
        });

        assert_eq!(
            res.correct as u32,
            (0..=range2)
                .map(|i| binomial(range2, i) * binomial(range1, i))
                .sum::<u32>()
        );
        assert_eq!(res.total(), 1 << (range1 + range2));
    }

    #[test]
    fn same_cardinality_implies_repr_but_more() {
        let mut encoder = CadicalEncoder::new();

        let range: u32 = 3;

        let mut constraint = SameCardinality::new();
        constraint
            .add_lits((0..range).map(Pos))
            .add_lits((range..2 * range).map(Pos))
            .add_lits((2 * range..3 * range).map(Pos))
            .add_lits((3 * range..4 * range).map(Pos));

        let repr = constraint.encode_constraint_implies_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );

        let res = constraint_implies_repr_tester(&mut encoder, repr, |model| {
            let c1 = model
                .vars()
                .filter(|l| (0..range).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            let c2 = model
                .vars()
                .filter(|l| (range..2 * range).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            let c3 = model
                .vars()
                .filter(|l| (2 * range..3 * range).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            let c4 = model
                .vars()
                .filter(|l| (3 * range..4 * range).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            c1 == c2 && c1 == c3 && c1 == c4
        });

        assert_eq!(
            res.correct as u32,
            (0..=range).map(|i| binomial(range, i).pow(4)).sum::<u32>()
        );
        assert_eq!(res.total(), 1 << (4 * range));
    }

    #[test]
    fn same_cardinality_equals_repr() {
        let mut encoder = CadicalEncoder::new();

        let range: u32 = 5;

        let mut constraint = SameCardinality::new();
        constraint
            .add_lits((0..range).map(Pos))
            .add_lits((range..2 * range).map(Pos));

        let repr = constraint.encode_constraint_equals_repr(
            None,
            &mut encoder.solver,
            &mut encoder.varmap,
        );

        let res = constraint_equals_repr_tester(&mut encoder, repr, |model| {
            let c1 = model
                .vars()
                .filter(|l| (0..range).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            let c2 = model
                .vars()
                .filter(|l| (range..2 * range).contains(l.var()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            c1 == c2
        });

        assert_eq!(
            res.correct as u32,
            (0..=range).map(|i| binomial(range, i).pow(2)).sum::<u32>()
        );
        assert_eq!(res.total(), 1 << (2 * range));
    }

    #[test]
    fn less_cardinality_constraint() {
        let mut encoder = CadicalEncoder::new();

        let range: u32 = 5;

        let constraint = LessCardinality {
            larger: (0..range).map(Pos),
            smaller: (range..2 * range).map(Pos),
        };

        encoder.add_constraint(constraint);

        let res = retry_until_unsat(&mut encoder, |model| {
            model.print_model();
            let c1 = model
                .vars()
                .filter(|v| (0..range).contains(&v.unwrap()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            let c2 = model
                .vars()
                .filter(|v| (range..2 * range).contains(&v.unwrap()))
                .filter(|l| matches!(l, Pos(_)))
                .count();
            assert!(c1 > c2);
        });
        assert_eq!(
            res as u32,
            (0..range)
                .map(|i| {
                    let smaller_combs = binomial(range, i);

                    smaller_combs
                        * (i + 1..=range).map(|i| binomial(range, i)).sum::<u32>()
                })
                .sum::<u32>(),
        );
    }
}
