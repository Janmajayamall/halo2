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

use crate::plonk::{Circuit, ConstraintSystem};
use ff::PrimeField;
use std::collections::HashMap;

pub struct Ir {}

struct Gate {
    name: &'static str,
    // expressions: Vec,
}

struct Variable {
    index: usize,
    col_type: ColType,
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

        cs.gates.iter().map(|gate| {
            gate.polynomials().iter().for_each(|c| {
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
                            col_type: ColType::Fixed(rotation.0),
                        }]
                    },
                    &|_, column, rotation| {
                        vec![Variable {
                            index: 0,
                            col_type: ColType::Advice(rotation.0),
                        }]
                    },
                    &|_, column, rotation| {
                        vec![Variable {
                            index: 0,
                            col_type: ColType::Instance(rotation.0),
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
                );
            });
        });
    }
}
