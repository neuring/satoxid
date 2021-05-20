use core::fmt::{self, Debug};
use std::collections::HashMap;

use crate::{Lit, SatVar, VarType};

/// Mapper from user defined variables and integer sat variables.
pub struct VarMap<V> {
    forward: HashMap<V, i32>,
    reverse: HashMap<i32, V>,
    next_id: i32,
}

impl<V> Default for VarMap<V> {
    fn default() -> Self {
        Self {
            forward: Default::default(),
            reverse: Default::default(),
            next_id: 1,
        }
    }
}

impl<V: Debug> Debug for VarMap<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map: Vec<_> = self.forward.iter().collect();
        map.sort_by_key(|&(_, &i)| i);

        f.debug_list().entries(map).finish()
    }
}

impl<V: SatVar> VarMap<V> {
    /// Translates an element of type `V` to a integer SAT variable used by the
    /// backend solver.
    /// If `var` wasn't already used it generates a new SAT variable.
    /// Depending on whether `var` is `Pos` or `Neg` the returned value is
    /// positive or negative.
    pub fn add_var(&mut self, lit: impl Into<VarType<V>>) -> i32 {
        let lit = lit.into();

        let lit = match lit {
            VarType::Named(lit) => lit,
            VarType::Unnamed(i) => return i,
        };

        let (var, pol) = match lit {
            Lit::Pos(v) => (v, 1),
            Lit::Neg(v) => (v, -1),
        };

        let id = if let Some(id) = self.forward.get(&var) {
            *id
        } else {
            let id = self.new_var();

            self.forward.insert(var.clone(), id);
            self.reverse.insert(id, var);

            id
        };

        pol * id
    }

    /// Same as `add_var` but it won't insert new `Lit<V>` instead returning `None`.
    pub fn get_var(&self, lit: impl Into<VarType<V>>) -> Option<i32> {
        let lit = lit.into();

        let lit = match lit {
            VarType::Named(lit) => lit,
            VarType::Unnamed(i) => return Some(i),
        };

        let (var, pol) = match lit {
            Lit::Pos(v) => (v, 1),
            Lit::Neg(v) => (v, -1),
        };

        Some(pol * self.forward.get(&var).copied()?)
    }

    /// Lookup the correct `V` based on the integer SAT variable.
    pub fn lookup(&self, lit: i32) -> Option<Lit<V>> {
        let var = self.reverse.get(&lit.abs())?.clone();

        if lit < 0 {
            Some(Lit::Neg(var))
        } else {
            Some(Lit::Pos(var))
        }
    }

    pub(crate) fn iter_internal_vars(&self) -> impl Iterator<Item = i32> {
        1..self.next_id
    }
}

impl<V> VarMap<V> {
    /// Generates fresh (unused) SAT variable.
    pub fn new_var(&mut self) -> i32 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }
}

