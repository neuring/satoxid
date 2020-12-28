use std::{collections::HashSet, fmt::Debug};

use crate::{Encoder, Lit, Model, SatVar, Solver};

use super::Clause;

pub fn retry_until_unsat<V: SatVar + Debug + Ord>(
    solver: &mut Solver<V>,
    pred: impl Fn(&Model<V>) -> bool,
) -> usize {
    let mut counter = 0;

    while let Some(model) = solver.solve() {
        assert!(pred(&model), "{:?}", &model);
        solver.add_constraint(Clause(model.vars().map(|l| -l)));
        counter += 1;
    }

    counter
}
