use std::marker::PhantomData;

use crate::{clause, Constraint, Encoder, SatVar, VarMap};

pub struct ClauseCollector<'a, V> {
    pub clauses: Vec<Vec<i32>>,
    pub varmap: &'a mut VarMap<V>,
}

impl<'a, V> From<&'a mut VarMap<V>> for ClauseCollector<'a, V> {
    fn from(varmap: &'a mut VarMap<V>) -> Self {
        Self {
            clauses: Vec::default(),
            varmap,
        }
    }
}

impl<'a, V: SatVar> Encoder<V> for ClauseCollector<'a, V> {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>,
    {
        self.clauses.push(lits.collect());
    }

    fn varmap(&mut self) -> &mut VarMap<V> {
        &mut self.varmap
    }
}

pub fn repr_implies_constraint<V, C, E>(constraint: C, repr: i32, solver: &mut E)
where
    V: SatVar,
    C: Constraint<V>,
    E: Encoder<V>,
{
    let mut wrapper = ClauseCollector::from(solver.varmap());

    constraint.encode(&mut wrapper);

    let ClauseCollector { clauses, .. } = wrapper;

    for clause in &clauses {
        solver.add_clause(clause.iter().copied().chain(clause!(-repr)));
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        constraints::{test_util::retry_until_unsat, Clause, AtMostK},
        Lit, Solver, VarType,
    };

    use super::*;
    #[test]
    fn repr_implies_constraint() {
        let lits = (1..=5).map(|i| Lit::Pos(i));
        let k = 2;
        let constraint = AtMostK { k, lits };

        let mut solver = Solver::new();
        let repr = solver.varmap().new_var();
        super::repr_implies_constraint(constraint, repr, &mut solver);
        solver.add_clause(clause![repr]);

        let res = retry_until_unsat(&mut solver, |model| {
            println!("{:?}", {
                let mut m = model.all_vars().collect::<Vec<_>>();
                m.sort();
                m
            });

            assert!(model.vars().filter(|v| v.is_pos()).count() <= k as usize);
        });
        assert_eq!(res, 16);
    }
}
