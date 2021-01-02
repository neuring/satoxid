use std::marker::PhantomData;

use crate::{clause, Constraint, Encoder, SatVar, Solver, VarMap};

#[derive(Default)]
pub struct ClauseCollector {
    pub clauses: Vec<Vec<i32>>,
}

impl Solver for ClauseCollector {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>,
    {
        self.clauses.push(lits.collect());
    }
}

pub fn repr_implies_constraint<V, C, S>(
    constraint: C,
    repr: i32,
    solver: &mut S,
    varmap: &mut VarMap<V>,
) where
    V: SatVar,
    C: Constraint<V>,
    S: Solver,
{
    let mut wrapper = ClauseCollector::default();

    constraint.encode(&mut wrapper, varmap);

    let clauses = wrapper.clauses;

    for clause in &clauses {
        solver.add_clause(clause.iter().copied().chain(clause!(-repr)));
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        constraints::{test_util::retry_until_unsat, AtMostK, Clause},
        Lit, Solver, VarType,
    };

    use super::*;
    #[test]
    fn repr_implies_constraint() {
        let lits = (1..=5).map(|i| Lit::Pos(i));
        let k = 2;
        let constraint = AtMostK { k, lits };

        let mut encoder = Encoder::<_, cadical::Solver>::new();
        let repr = encoder.varmap.new_var();
        super::repr_implies_constraint(constraint, repr, &mut encoder.solver, &mut encoder.varmap);
        encoder.solver.add_clause(clause![repr]);

        let res = retry_until_unsat(&mut encoder, |model| {
            model.print_model();
            assert!(model.vars().filter(|v| v.is_pos()).count() <= k as usize);
        });
        assert_eq!(res, 16);
    }
}
