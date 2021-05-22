use core::fmt::{self, Debug};
use std::collections::HashMap;

use crate::{Lit, SatVar, VarType};

/// Mapper from user defined variables and integer sat variables.
pub struct VarMap<V> {
    forward: HashMap<V, i32>,
    reverse: HashMap<i32, V>,
    next_id: i32,
}

impl<V: SatVar> PartialEq for VarMap<V> {
    fn eq(&self, other: &Self) -> bool {
        self.next_id == other.next_id && self.forward == other.forward
    }
}

impl<V: SatVar> Eq for VarMap<V> {}

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

#[cfg(feature = "serde")]
mod serde {
    use super::*;
    use ::serde::{
        de::{self, MapAccess, SeqAccess, Visitor},
        ser::SerializeStruct,
        Deserialize, Deserializer, Serialize, Serializer
    };

    impl<V: Serialize + SatVar> Serialize for VarMap<V> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let mut struct_serializer = serializer.serialize_struct("VarMap", 2)?;

            let vars = self.next_id - 1;

            struct_serializer.serialize_field("vars", &vars)?;

            struct_serializer.serialize_field("mapping", &self.reverse)?;

            struct_serializer.end()
        }
    }

    impl<'de, V: SatVar + Deserialize<'de>> Deserialize<'de> for VarMap<V> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            enum Field {
                Vars,
                Mapping,
            }

            impl<'de> Deserialize<'de> for Field {
                fn deserialize<D>(deserializer: D) -> Result<Field, D::Error>
                where
                    D: Deserializer<'de>,
                {
                    struct FieldVisitor;

                    impl<'de> Visitor<'de> for FieldVisitor {
                        type Value = Field;

                        fn expecting(
                            &self,
                            formatter: &mut fmt::Formatter,
                        ) -> fmt::Result {
                            formatter.write_str("`vars` or `mapping`")
                        }

                        fn visit_str<E>(self, value: &str) -> Result<Field, E>
                        where
                            E: de::Error,
                        {
                            match value {
                                "vars" => Ok(Field::Vars),
                                "mapping" => Ok(Field::Mapping),
                                _ => Err(de::Error::unknown_field(value, FIELDS)),
                            }
                        }
                    }

                    deserializer.deserialize_identifier(FieldVisitor)
                }
            }

            struct VarMapVisitor<VAR>(std::marker::PhantomData<VAR>);

            impl<'de, VAR: SatVar + Deserialize<'de>> Visitor<'de> for VarMapVisitor<VAR> {
                type Value = VarMap<VAR>;

                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    write!(
                        formatter,
                        "struct VarMap<{}>",
                        std::any::type_name::<VAR>()
                    )
                }

                fn visit_seq<V>(self, mut seq: V) -> Result<VarMap<VAR>, V::Error>
                where
                    V: SeqAccess<'de>,
                {
                    let vars: i32 = seq
                        .next_element()?
                        .ok_or_else(|| de::Error::invalid_length(0, &self))?;
                    let next_id = vars + 1;

                    let reverse_map: HashMap<i32, VAR> = seq
                        .next_element()?
                        .ok_or_else(|| de::Error::invalid_length(1, &self))?;

                    let forward_map =
                        reverse_map.iter().map(|(&k, v)| (v.clone(), k)).collect();

                    Ok(VarMap {
                        forward: forward_map,
                        reverse: reverse_map,
                        next_id,
                    })
                }

                fn visit_map<V>(self, mut map: V) -> Result<VarMap<VAR>, V::Error>
                where
                    V: MapAccess<'de>,
                {
                    let mut next_id = None;
                    let mut reverse_map = None;

                    while let Some(key) = map.next_key()? {
                        match key {
                            Field::Vars => {
                                if next_id.is_some() {
                                    return Err(de::Error::duplicate_field(
                                        "vars",
                                    ));
                                }
                                next_id = Some(map.next_value()?);
                            }
                            Field::Mapping => {
                                if reverse_map.is_some() {
                                    return Err(de::Error::duplicate_field(
                                        "mapping",
                                    ));
                                }
                                reverse_map = Some(map.next_value()?);
                            }
                        }
                    }

                    let vars: i32 = next_id
                        .ok_or_else(|| de::Error::missing_field("next_id"))?;
                    let next_id = vars + 1;

                    let reverse_map: HashMap<i32, VAR> = reverse_map
                        .ok_or_else(|| de::Error::missing_field("mapping"))?;
                    let forward_map =
                        reverse_map.iter().map(|(&k, v)| (v.clone(), k)).collect();

                    Ok(VarMap {
                        forward: forward_map,
                        reverse: reverse_map,
                        next_id,
                    })
                }
            }

            const FIELDS: &'static [&'static str] = &["vars", "mapping"];
            deserializer.deserialize_struct(
                "VarMap",
                FIELDS,
                VarMapVisitor(Default::default()),
            )
        }
    }
}

#[cfg(all(test, feature = "serde"))]
mod tests {
    use super::VarMap;
    use crate::Lit::*;

    use ::serde::{Deserialize, Serialize};

    #[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
    enum SatVar {
        A(i32, bool),
        B(String),
    }

    #[test]
    fn serde_test() {

        let mut varmap = VarMap::<SatVar>::default();

        varmap.add_var(Pos(SatVar::A(0, true)));
        varmap.add_var(Pos(SatVar::A(1, true)));
        varmap.add_var(Pos(SatVar::A(2, false)));
        varmap.add_var(Pos(SatVar::A(4, true)));
        varmap.add_var(Pos(SatVar::B("hey".into())));
        varmap.add_var(Pos(SatVar::B("listen".into())));

        let s = serde_json::to_string(&varmap).unwrap();

        let parsed_json: serde_json::Value = serde_json::from_str(&s).unwrap();

        let json = serde_json::json!({
            "vars" : 6, 
            "mapping" : {
                "1": {"A" : [0, true]},
                "2": {"A" : [1, true]},
                "3": {"A" : [2, false]},
                "4": {"A" : [4, true]},
                "5": {"B" : "hey"},
                "6": {"B" : "listen"},
            },
        });

        assert_eq!(json, parsed_json);

        let v = serde_json::from_str(&s).unwrap();

        assert_eq!(varmap, v);
    }
}
