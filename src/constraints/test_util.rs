use std::{collections::HashSet, fmt::Debug};

use crate::{Encoder, Lit, Model, SatVar, Solver, VarMap};

use super::Clause;

pub fn retry_until_unsat<V: SatVar + Ord>(
    encoder: &mut Encoder<V, cadical::Solver>,
    mut pred: impl FnMut(&Model<V>),
) -> usize {
    let mut counter = 0;

    while let Some(model) = encoder.solve() {
        pred(&model);
        let varmap = &mut encoder.varmap;
        encoder
            .solver
            .add_clause(model.vars().map(|l| varmap.get_var(!l).unwrap()));
        counter += 1;
    }

    counter
}
