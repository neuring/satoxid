use crate::{clause, Solver};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Direction {
    Both,
    InToOut,
    OutToIn,
}

impl Direction {
    fn in_to_out(&self) -> bool {
        match self {
            Direction::Both => true,
            Direction::InToOut => true,
            Direction::OutToIn => false,
        }
    }

    fn out_to_in(&self) -> bool {
        match self {
            Direction::Both => true,
            Direction::InToOut => false,
            Direction::OutToIn => true,
        }
    }
}

/// Helper struct to build SAT encoding using circuits.
pub struct Circuit<'a, S> {
    pub solver: &'a mut S,
    pub dir: Direction,
}

impl<'a, S: Solver> Circuit<'a, S> {
    /// Construct a new circuit encoded using `solver`.
    pub fn new(solver: &'a mut S, dir: Direction) -> Self {
        Self { solver, dir }
    }

    pub fn and_gate<I>(&mut self, i: I, o: i32)
    where
        I: Iterator<Item = i32> + Clone,
    {
        if self.dir.in_to_out() {
            self.solver
                .add_clause(i.clone().map(|l| -l).chain(clause![o]));
        }

        if self.dir.out_to_in() {
            for lit in i {
                self.solver.add_clause(clause![-o, lit]);
            }
        }
    }

    pub fn or_gate<I>(&mut self, i: I, o: i32)
    where
        I: Iterator<Item = i32> + Clone,
    {
        if self.dir.in_to_out() {
            for lit in i.clone() {
                self.solver.add_clause(clause![-lit, o]);
            }
        }

        if self.dir.out_to_in() {
            self.solver.add_clause(i.chain(clause![-o]));
        }
    }

    pub fn equal(&mut self, i: i32, o: i32) {
        if self.dir.in_to_out() {
            self.solver.add_clause(clause![-i, o]);
        }

        if self.dir.out_to_in() {
            self.solver.add_clause(clause![-o, i]);
        }
    }

    pub fn set_zero(&mut self, i: i32) {
        self.solver.add_clause(clause![-i]);
    }

    pub fn set_one(&mut self, i: i32) {
        self.solver.add_clause(clause![i]);
    }
}
