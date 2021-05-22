# Satoxid, a SATisfiability encoding library

Satoxid is a library to help with encoding SAT problems with a focus on ergonomics and debugability.

## Features
 * Predefined common constraints
 * Variables are values of a user defined type instead of integers
 * Modular, you can implement your own constraints and backends

## Example
```rust
use satoxid::{CadicalEncoder, constraints::ExactlyK};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Var {
    A, B, C
}

use Var::*;

fn main() {
    let mut encoder = CadicalEncoder::new();

    let constraint = ExactlyK { k: 1, lits: [A, B, C].iter().copied() };

    encoder.add_constraint(constraint);

    if let Some(model) = encoder.solve() {
        let true_vars = model.vars().filter(|v| v.is_pos()).count();
        assert_eq!(true_vars, 1);
    }
}
```
