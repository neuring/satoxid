use std::collections::HashMap;

use anyhow::Context;
use itertools::iproduct;
use satoxid::{
    constraints::{AtLeastK, ExactlyK},
    Backend, CadicalEncoder, Encoder, Model,
};
use structopt::StructOpt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Tile {
    x: u32,     /* 0..9 */
    y: u32,     /* 0..9 */
    value: u32, /* 1..=9 */
}

fn encode_sudoku_rules(encoder: &mut Encoder<Tile, impl Backend>) {
    // Each Tile must have exactly one value
    for (x, y) in iproduct!(0..9, 0..9) {
        let lits = (1..=9).map(|value| Tile { x, y, value });
        let constraint = ExactlyK { k: 1, lits };
        encoder.add_constraint(constraint);
    }

    // Every value appears in every row.
    for (row, value) in iproduct!(0..9, 1..=9) {
        let lits = (0..9).map(|col| Tile {
            x: col,
            y: row,
            value,
        });
        let constraint = AtLeastK { k: 1, lits };
        encoder.add_constraint(constraint);
    }

    // Every value appears in every col.
    for (col, value) in iproduct!(0..9, 1..=9) {
        let lits = (0..9).map(|row| Tile {
            x: col,
            y: row,
            value,
        });
        let constraint = AtLeastK { k: 1, lits };
        encoder.add_constraint(constraint);
    }

    // Every value appears in every 3x3 square.
    for (square_x, square_y, value) in iproduct!(0..3, 0..3, 1..=9) {
        let lits = iproduct!(0..3, 0..3).map(|(x, y)| Tile {
            x: 3 * square_x + x,
            y: 3 * square_y + y,
            value,
        });
        let constraint = AtLeastK { k: 1, lits };
        encoder.add_constraint(constraint);
    }
}

fn parse_input(input: &str) -> anyhow::Result<HashMap<(u32, u32), u32>> {
    let mut result = HashMap::new();

    for (row_idx, line) in input.trim().split(';').enumerate() {
        for (col_idx, val) in line.trim().split(',').enumerate() {
            let val = val
                .parse()
                .with_context(|| format!("Invalid value: '{}'", val))?;

            if val > 0 {
                result.insert((col_idx as u32, row_idx as u32), val);
            }
        }
    }

    Ok(result)
}

fn print_solution_from_model(model: &Model<Tile>) {
    for y in 0..9 {
        for x in 0..9 {
            let v: Vec<_> = (1..=9)
                .filter(|&value| model.var(Tile { x, y, value }).unwrap())
                .collect();
            assert_eq!(v.len(), 1);
            print!("{} ", v[0]);
        }
        println!();
    }
}

#[derive(structopt::StructOpt)]
/// Simple sudoku solver.
///
/// Enter a sudoku in the following format.
/// Example:
/// "0,0,0,8,0,0,0,0,5;
/// 8,4,0,7,0,3,0,0,0;
/// 0,1,2,0,0,6,0,3,0;
/// 7,9,1,3,6,0,8,4,0;
/// 6,8,0,9,2,0,3,5,1;
/// 0,0,0,1,4,0,0,0,7;
/// 0,7,8,0,0,0,5,0,6;
/// 2,0,0,0,0,1,0,0,0;
/// 0,0,0,6,0,0,2,8,0"
///
/// Rows are separated by semicolons and every value in a row by a comma.
///
/// Zeros represent empty fields.
struct Options {
    /// Sudoku data in the specified format.
    sudoku: String,
}

fn main() -> anyhow::Result<()> {
    let arg = Options::from_args();

    let sudoku = parse_input(&arg.sudoku)?;

    let mut encoder = CadicalEncoder::new();

    encode_sudoku_rules(&mut encoder);

    // Set defined tiles.
    for (&(x, y), &value) in sudoku.iter() {
        encoder.add_constraint(Tile { x, y, value })
    }

    if let Some(model) = encoder.solve() {
        print_solution_from_model(&model);
    } else {
        println!("No solution exists!");
    }

    Ok(())
}
