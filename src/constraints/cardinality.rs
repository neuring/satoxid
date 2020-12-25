use core::fmt;
use std::{fmt::Debug, iter::once};

use crate::{Constraint, Encoder, Lit, SatVar, clause};

/// This constraint encodes the requirement that at most `k` of `lits` variables 
/// are true.
#[derive(Clone)]
pub struct AtMostK<I> {
    pub lits: I,
    pub k: u32,
}

impl<V, I> Constraint<V> for AtMostK<I>
where
    V: SatVar + Clone + Debug,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode<E: Encoder<V>>(self, solver: &mut E) {

        if self.k == 0 {
            for v in self.lits {
                let v = solver.varmap().add_var(-v);
                solver.add_clause(once(v));
            }
            return;
        }

        let vars: Vec<_> = self.lits.map(|v| solver.varmap().add_var(v)).collect();
        let n = vars.len();
        let k = self.k as usize;

        let mut prev_s: Vec<_> = (0..k).map(|_| solver.varmap().new_var()).collect();

        if let Some(v) = vars.first() {
            solver.add_clause(clause!(-v, prev_s[0]));
        } else {
            return;
        }

        for s in prev_s.iter().skip(1) {
            solver.add_clause(clause!(-s));
        }

        for (i, v) in vars.iter().enumerate().skip(1) {
            if i + 1 == n {
                solver.add_clause(clause!(-v, -prev_s[k - 1]));
                break;
            }

            let new_s: Vec<_> = (0..k).map(|_| solver.varmap().new_var()).collect();

            solver.add_clause(clause!(-v, new_s[0]));
            solver.add_clause(clause!(-prev_s[0], new_s[0]));

            for j in 1usize..(k as usize) {
                solver.add_clause(clause!(-v, -prev_s[j - 1], new_s[j]));
                solver.add_clause(clause!(-prev_s[j], new_s[j]));
            }

            solver.add_clause(clause!(-v, -prev_s[k - 1]));
            prev_s = new_s;
        }
    }
}

impl<V: Debug, I> Debug for AtMostK<I>
where
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<_> = self.lits.clone().collect();

        f.debug_struct("AtMostK")
            .field("k", &self.k)
            .field("vars", &lits)
            .finish()
    }
}

/// This constraint encodes the requirement that atleast `k` of `lits` variables 
/// are true.
#[derive(Clone)]
pub struct AtleastK<I> {
    pub lits: I,
    pub k: u32,
}

impl<V, I> Constraint<V> for AtleastK<I>
where
    V: SatVar + Debug + Clone,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let k = self.k as usize;

        let vars: Vec<_> = self.lits.map(|v| solver.varmap().add_var(v)).collect();

        if k == 0 {
            return;
        } else
        if k == 1 {
            solver.add_clause(vars.into_iter());
            return;
        }

        let n = vars.len();

        let mut prev_s: Vec<_> = (0..k).map(|_| solver.varmap().new_var()).collect();

        solver.add_clause(clause!(vars[0], prev_s[k - 1]));
        solver.add_clause(clause!(prev_s[k - 1], prev_s[k - 2]));

        for (i, &v) in vars.iter().enumerate().skip(1) {
            if i + 1 == n {
                solver.add_clause(clause!(-prev_s[0], v));
                for j in 1..k {
                    solver.add_clause(clause!(-prev_s[j]));
                }

                break;
            }

            let mut new_s: Vec<_> = (0..k).map(|_| solver.varmap().new_var()).collect();

            solver.add_clause(clause!(-prev_s[0], new_s[0], v));

            for j in 1..k {
                solver.add_clause(clause!(-prev_s[j], new_s[j], v));
                solver.add_clause(clause!(-prev_s[j], new_s[j], new_s[j - 1]));
            }

            std::mem::swap(&mut prev_s, &mut new_s);
        }
    }
}

impl<V: Debug, I> Debug for AtleastK<I>
where
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<_> = self.lits.clone().collect();

        f.debug_struct("AtleastK")
            .field("k", &self.k)
            .field("vars", &lits)
            .finish()
    }
}

