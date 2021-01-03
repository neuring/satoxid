use std::{collections::HashSet, fmt::Debug, iter::once};

use crate::{clause, Encoder, Lit, Model, SatVar, Solver, VarMap, VarType};

use super::Clause;

pub fn retry_until_unsat<V: SatVar + Ord>(
    encoder: &mut Encoder<V>,
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

/// Struct which contains 
pub struct ConstraintTestResult {
    pub correct: usize,
    pub incorrect: usize,
}

impl ConstraintTestResult {
    pub fn total(&self) -> usize {
        self.correct + self.incorrect
    }
}

/// Test function for ConstraintRepr implementation.
/// Provide a predicate that returns whether the model satisifies the constraint.
/// If it does we check that repr is true and that it cannot be false.
/// If it doesn't we check if repr could be both true and false.
/// Returns the number of times the model was true.
pub fn constraint_implies_repr_tester<V: SatVar + Ord>(
    encoder: &mut Encoder<V>,
    repr: i32,
    mut pred: impl FnMut(&Model<V>) -> bool,
) -> ConstraintTestResult {
    let mut correct_counter = 0;
    let mut incorrect_counter = 0;

    while let Some(model) = encoder.solve() {
        let varmap = &mut encoder.varmap;

        model.print_model();

        let internal = &mut encoder.solver;

        let vars = || model.vars().map(|l| varmap.get_var(l).unwrap());

        if pred(&model) {
            let repr_assignment = model.lit_internal(VarType::Unnamed(repr));
            assert!(repr_assignment);
            assert!(!internal.solve_with(vars().chain(once(-repr))).unwrap());
            correct_counter += 1;
        } else {

            assert!(internal.solve_with(vars().chain(once(repr))).unwrap());
            assert!(internal.solve_with(vars().chain(once(-repr))).unwrap());
            incorrect_counter += 1;
        }

        let clause: Vec<_> = model
            .vars()
            .map(|l| varmap.get_var(!l).unwrap())
            .collect();

        encoder.solver.add_clause(clause.into_iter());

    }

    ConstraintTestResult {correct: correct_counter, incorrect: incorrect_counter}
}

/// Test function for ConstraintRepr implementation.
/// Provide a predicate that returns whether the model satisifies the constraint.
/// If it does we check that repr is true and that it cannot be false.
/// If it doesn't we check if repr is false and that it cannot be true.
/// Returns the number of times the model was true.
pub fn constraint_equals_repr_tester<V: SatVar + Ord>(
    encoder: &mut Encoder<V>,
    repr: i32,
    mut pred: impl FnMut(&Model<V>) -> bool,
) -> ConstraintTestResult {
    let mut correct_counter = 0;
    let mut incorrect_counter = 0;

    while let Some(model) = encoder.solve() {
        let varmap = &mut encoder.varmap;

        model.print_model();

        let internal = &mut encoder.solver;

        let vars = || model.vars().map(|l| varmap.get_var(l).unwrap());

        if pred(&model) {
            let repr_assignment = model.lit_internal(VarType::Unnamed(repr));
            assert!(repr_assignment);
            assert!(!internal.solve_with(vars().chain(once(-repr))).unwrap());
            correct_counter += 1;
        } else {

            assert!(!internal.solve_with(vars().chain(once(repr))).unwrap());
            assert!(internal.solve_with(vars().chain(once(-repr))).unwrap());
            incorrect_counter += 1;
        }

        let clause: Vec<_> = model
            .vars()
            .map(|l| varmap.get_var(!l).unwrap())
            .collect();

        encoder.solver.add_clause(clause.into_iter());

    }

    ConstraintTestResult { correct: correct_counter, incorrect: incorrect_counter }
}
