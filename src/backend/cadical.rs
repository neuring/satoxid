use std::fmt;

use crate::{Backend, Encoder, Solver};

/// Encoder using the CaDiCal Sat solver.
pub type CadicalEncoder<V> = Encoder<V, cadical::Solver>;

impl Backend for cadical::Solver {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>,
    {
        self.add_clause(lits.into_iter());
    }

    fn add_debug_info<D: fmt::Debug>(&mut self, debug: D) {
        println!("{:+?}", debug)
    }
}

impl Solver for cadical::Solver {
    fn solve(&mut self) -> bool {
        self.solve().unwrap_or(false)
    }

    fn value(&self, var: i32) -> bool {
        self.value(var).unwrap_or(true)
    }
}
