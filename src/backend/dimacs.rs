use std::fmt;

use crate::Backend;

enum DimacsEntry {
    Clause(Vec<i32>),
    Comment(String),
}

#[derive(Default)]
pub struct DimacsWriter {
    max_var: i32,
    data: Vec<DimacsEntry>,
}

impl DimacsWriter {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn write_to(&self, mut writer: impl std::io::Write) -> std::io::Result<()> {
        let clause_count = self
            .data
            .iter()
            .filter(|e| matches!(e, DimacsEntry::Clause(..)))
            .count();

        writeln!(writer, "p cnf {} {}", self.max_var, clause_count)?;

        for entry in &self.data {
            match entry {
                DimacsEntry::Clause(clause) => {
                    for l in clause {
                        write!(writer, "{} ", l)?
                    }
                    writeln!(writer, "0")?;
                },
                DimacsEntry::Comment(s) => {
                    for line in s.lines() {
                        writeln!(writer, "c {}", line)?;
                    }
                }
            }
        }

        Ok(())
    }
}

impl Backend for DimacsWriter {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>,
    {
        let clause: Vec<_> = lits.collect();

        for &lit in clause.iter() {
            self.max_var = self.max_var.max(lit.abs());
        }

        self.data.push(DimacsEntry::Clause(clause));
    }

    fn add_debug_info<D: fmt::Debug>(&mut self, debug: D) {
        self.data
            .push(DimacsEntry::Comment(format!("{:#?}", debug)));
    }

    fn append_debug_info<D: fmt::Debug>(&mut self, debug: D) {
        if let Some(DimacsEntry::Comment(s)) = self.data.last_mut() {
            s.push_str(&format!("{:?}", debug));
        }
    }
}
