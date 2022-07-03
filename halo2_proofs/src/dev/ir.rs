//! IR for Plonk.
//!

// variables: [
//     {
//         index: 0,
//         type: advice
//     }
// ],
// gates: [
//     {
//         name,
//         expressions: [
//             exp1 (uses variables index from `variables`),
//             ..
//             ..
//         ]
//     }
// ]

use super::util;
use crate::plonk::{Circuit, ConstraintSystem};
use ff::PrimeField;
use std::collections::HashMap;
use std::fmt;

pub struct Ir {}

struct Constraint {
    name: &'static str,
    expression: String,
}

struct Gate {
    name: &'static str,
    constraints: Vec<Constraint>,
}

struct Variable {
    index: usize,
    col_type: ColType,
}

impl Variable {
    /// key = (col_type, column_index, rotation)
    /// rotation is always `0` for selector column
    fn key(&self) -> (usize, usize, i32) {
        match self.col_type {
            ColType::Advice(c_i, r) => (0, c_i, r),
            ColType::Fixed(c_i, r) => (1, c_i, r),
            ColType::Instance(c_i, r) => (2, c_i, r),
            ColType::Selector(c_i) => (3, c_i, 0),
        }
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.col_type {
            ColType::Advice(c_i, r) => write!(f, "A{}", self.index),
            ColType::Fixed(c_i, r) => write!(f, "F{}", self.index),
            ColType::Instance(c_i, r) => write!(f, "I{}", self.index),
            ColType::Selector(c_i) => write!(f, "S{}", self.index),
        }
    }
}

enum ColType {
    Advice(usize, i32),
    Fixed(usize, i32),
    Instance(usize, i32),
    Selector(usize),
}

impl Ir {
    pub fn collect<F: PrimeField, C: Circuit<F>>() {
        let mut cs = ConstraintSystem::default();
        let _ = C::configure(&mut cs);
        let cs = cs;

        // Creates a hashmap with all `Variable`s
        let variables_vec = cs.gates.iter().flat_map(|gate| {
            gate.polynomials().iter().flat_map(|c| {
                c.evaluate(
                    &|_| vec![],
                    &|selector| {
                        vec![Variable {
                            index: 0,
                            col_type: ColType::Selector(selector.0),
                        }]
                    },
                    &|_, column, rotation| {
                        vec![Variable {
                            index: 0,
                            col_type: ColType::Fixed(column, rotation.0),
                        }]
                    },
                    &|_, column, rotation| {
                        vec![Variable {
                            index: 0,
                            col_type: ColType::Advice(column, rotation.0),
                        }]
                    },
                    &|_, column, rotation| {
                        vec![Variable {
                            index: 0,
                            col_type: ColType::Instance(column, rotation.0),
                        }]
                    },
                    &|a| a,
                    &|mut a, mut b| {
                        a.append(&mut b);
                        a
                    },
                    &|mut a, mut b| {
                        a.append(&mut b);
                        a
                    },
                    &|a, _| a,
                )
            })
        });
        let mut variables_map = HashMap::new();
        let mut index: usize = 0;
        variables_vec.for_each(|v| {
            let v = variables_map.entry(v.key()).or_insert(v);
            v.index = index;
            index += 1;
        });

        // Collect all gates
        let gates = cs.gates.iter().map(|gate| Gate {
            name: gate.name(),
            constraints: gate
                .polynomials()
                .iter()
                .enumerate()
                .map(|(i, constraint)| Constraint {
                    name: gate.constraint_name(i),
                    expression: constraint.evaluate(
                        &util::format_value,
                        &|selector| {
                            format!(
                                "{}",
                                variables_map
                                    .get(&(3, selector.0, 0))
                                    .expect("Var key exists")
                            )
                        },
                        &|_, column, rotation| {
                            format!(
                                "{}",
                                variables_map
                                    .get(&(1, column, rotation.0))
                                    .expect("Var key exists")
                            )
                        },
                        &|_, column, rotation| {
                            format!(
                                "{}",
                                variables_map
                                    .get(&(0, column, rotation.0))
                                    .expect("Var key exists")
                            )
                        },
                        &|_, column, rotation| {
                            format!(
                                "{}",
                                variables_map
                                    .get(&(2, column, rotation.0))
                                    .expect("Var key exists")
                            )
                        },
                        &|a| {
                            if a.contains(' ') {
                                format!("-({})", a)
                            } else {
                                format!("-{}", a)
                            }
                        },
                        &|a, b| {
                            if let Some(b) = b.strip_prefix('-') {
                                format!("{} - {}", a, b)
                            } else {
                                format!("{} + {}", a, b)
                            }
                        },
                        &|a, b| match (a.contains(' '), b.contains(' ')) {
                            (false, false) => format!("{} * {}", a, b),
                            (false, true) => format!("{} * ({})", a, b),
                            (true, false) => format!("({}) * {}", a, b),
                            (true, true) => format!("({}) * ({})", a, b),
                        },
                        &|a, s| {
                            if a.contains(' ') {
                                format!("({}) * {}", a, util::format_value(s))
                            } else {
                                format!("{} * {}", a, util::format_value(s))
                            }
                        },
                    ),
                })
                .collect(),
        });
    }
}
