use std::{collections::HashSet, fmt::Debug};

use crate::{Encoder, Lit, Model, SatVar, Solver};

use super::Clause;

pub fn retry_until_unsat<V: SatVar + Ord>(
    solver: &mut Solver<V>,
    mut pred: impl FnMut(&Model<V>),
) -> usize {
    let mut counter = 0;

    while let Some(model) = solver.solve() {
        pred(&model);
        solver.add_constraint(Clause(model.vars().map(|l| -l)));
        counter += 1;
    }

    counter
}
