//! IR for Plonk.

// metadata: {"name": "MyCircuit", ...}
// config: {"nrows": 5, "ninstance": 2, "nadvice: 10", "nfixed": 4}
// constraints: [(F, 0, 1) * ((A, 1, 0) + (I, 0, -1)), ... ]
// fixed: [[1,2,3], [4,5,6], ...]
// copies: [((I,0,0), (A,1,2)), ...]
// halo2.gates: [ {name: "gate name", constraints: [{0 : "contraint 0"}, {3: "constraint 3"}]}]

use super::util;
use crate::circuit::Value;
use crate::plonk::{
    Advice, Any, Assigned, Assignment, Circuit, Column, ColumnType, ConstraintSystem, Error, Fixed,
    FloorPlanner, Instance, Selector,
};
use crate::poly::Rotation;
use ff::Field;
use pasta_curves::arithmetic::FieldExt;
use std::collections::HashMap;
use std::fmt;
use std::io;
use std::ops::Index;
use std::path::Ancestors;
use std::slice::SliceIndex;

#[derive(Debug)]
pub enum Polynomial<F: Field> {
    Var(Variable),
    Scalar(F),
    Neg(Box<Polynomial<F>>),
    Add(Box<Polynomial<F>>, Box<Polynomial<F>>),
    Mul(Box<Polynomial<F>>, Box<Polynomial<F>>),
}

#[derive(Debug)]
pub struct Constraint<F: Field> {
    name: &'static str,
    expression: Polynomial<F>,
}

#[derive(Debug)]
pub struct Gate<F: Field> {
    name: &'static str,
    constraints: Vec<Constraint<F>>,
}
#[derive(Debug)]
pub struct Variable {
    column_type: Any,
    index: usize,
    offset: i32,
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.column_type {
            Any::Advice => write!(f, "A{{{},{}}}", self.index, self.offset),
            Any::Fixed => write!(f, "F{{{},{}}}", self.index, self.offset),
            Any::Instance => write!(f, "I{{{},{}}}", self.index, self.offset),
        }
    }
}

impl<F: Field> fmt::Display for Polynomial<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var(v) => write!(f, "{}", v),
            Self::Scalar(v) => write!(f, "{}", &util::format_value(*v)),
            Self::Neg(x) => write!(f, "-{}", x),
            Self::Add(x, y) => match &**y {
                Self::Neg(y) => write!(f, "({} - {})", x, y),
                _ => write!(f, "({} + {})", x, y),
            },
            Self::Mul(x, y) => write!(f, "({} * {})", x, y),
        }
    }
}

impl<F: Field> fmt::Display for Constraint<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.name.is_empty() {
            write!(f, "{}", self.expression)
        } else {
            write!(f, "{}: {}", self.name, self.expression)
        }
    }
}

impl<F: Field> fmt::Display for Gate<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.name.is_empty() {
            write!(f, "[")?
        } else {
            write!(f, "{}: [", self.name)?
        }
        for c in &self.constraints {
            write!(f, "{}, ", c)?
        }
        write!(f, "]")
    }
}

/// IR struct
#[derive(Debug)]
pub struct Ir<F: Field> {
    k: u32,
    num_rows: usize,
    fixed: Vec<Vec<F>>,
    selectors: Vec<Vec<bool>>,
    equality: Vec<(Column<Any>, usize, Column<Any>, usize)>,
    constraints: Vec<Constraint<F>>,
    // Start of selector fixed columns
    selector_index: usize,
}

impl<F: FieldExt> Ir<F> {
    fn new(k: u32, num_fixed: usize, num_selectors: usize) -> Self {
        let num_rows = 1 << k;
        Self {
            k,
            num_rows,
            fixed: vec![vec![F::default(); num_rows]; num_fixed],
            selectors: vec![vec![false; num_rows]; num_selectors],
            equality: vec![],
            constraints: vec![],
            selector_index: num_fixed,
        }
    }

    /// Collects gates
    pub fn write<ConcreteCircuit: Circuit<F>>(
        k: u32,
        circuit: &ConcreteCircuit,
        compress: bool,
        outfile: impl io::Write,
    ) {
        let mut cs = ConstraintSystem::default();
        let config = ConcreteCircuit::configure(&mut cs);
        let mut ir = Ir::new(k, cs.num_fixed_columns, cs.num_selectors);
        ConcreteCircuit::FloorPlanner::synthesize(&mut ir, circuit, config, cs.constants.clone())
            .unwrap();

        if compress {
            let (cs_compressed, selector_polys) = cs.compress_selectors(ir.selectors.clone());
            assert!(cs_compressed.num_fixed_columns == ir.selector_index + selector_polys.len());
            cs = cs_compressed;
            ir.fixed.extend(selector_polys)
        } else {
            ir.fixed.extend(
                ir.selectors
                    .iter()
                    .map(|r| r.iter().map(|&s| F::from_u128(s as u128)).collect())
                    .collect::<Vec<_>>(),
            );
        }
        let gates = ir.collect_gates(cs);
    }

    fn collect_gates(&mut self, cs: ConstraintSystem<F>) -> Vec<Gate<F>> {
        cs.gates
            .iter()
            .map(|gate| Gate {
                name: gate.name(),
                constraints: gate
                    .polynomials()
                    .iter()
                    .enumerate()
                    .map(|(i, constraint)| Constraint {
                        name: gate.constraint_name(i),
                        expression: constraint.evaluate(
                            &Polynomial::Scalar,
                            &|selector| {
                                Polynomial::Var(Variable {
                                    column_type: Any::Fixed,
                                    index: self.selector_index + selector.0,
                                    offset: 0,
                                })
                            },
                            &|_, column, rotation| {
                                Polynomial::Var(Variable {
                                    column_type: Any::Fixed,
                                    index: column,
                                    offset: rotation.0,
                                })
                            },
                            &|_, column, rotation| {
                                Polynomial::Var(Variable {
                                    column_type: Any::Advice,
                                    index: column,
                                    offset: rotation.0,
                                })
                            },
                            &|_, column, rotation| {
                                Polynomial::Var(Variable {
                                    column_type: Any::Instance,
                                    index: column,
                                    offset: rotation.0,
                                })
                            },
                            &|x| Polynomial::Neg(Box::new(x)),
                            &|x, y| Polynomial::Add(Box::new(x), Box::new(y)),
                            &|x, y| Polynomial::Mul(Box::new(x), Box::new(y)),
                            &|a, s| Polynomial::Mul(Box::new(Polynomial::Scalar(s)), Box::new(a)),
                        ),
                    })
                    .collect(),
            })
            .collect()
    }
}

impl<F: Field> Assignment<F> for Ir<F> {
    fn enter_region<NR, N>(&mut self, _name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // TODO: Regions
    }

    fn exit_region(&mut self) {
        //TODO
    }

    fn enable_selector<A, AR>(
        &mut self,
        _annotation: A,
        selector: &Selector,
        row: usize,
    ) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if let Some(cell) = self.selectors[selector.0].get_mut(row) {
            *cell = true;
        } else {
            return Err(Error::not_enough_rows_available(self.k));
        };
        Ok(())
    }

    fn query_instance(&self, _column: Column<Instance>, _row: usize) -> Result<Value<F>, Error> {
        Ok(Value::unknown())
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _annotation: A,
        _column: Column<Advice>,
        _row: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> crate::circuit::Value<VR>,
        VR: Into<crate::plonk::Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _annotation: A,
        column: Column<Fixed>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<crate::plonk::Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let cell = self
            .fixed
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or(Error::BoundsFailure)?;
        *cell = to().into_field().evaluate().assign()?;
        Ok(())
    }

    fn copy(
        &mut self,
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) -> Result<(), Error> {
        self.equality
            .push((left_column, left_row, right_column, right_row));
        Ok(())
    }

    fn fill_from_row(
        &mut self,
        column: Column<Fixed>,
        row: usize,
        to: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        for row in row..self.num_rows {
            self.assign_fixed(|| "", column, row, || to)?;
        }
        Ok(())
    }

    fn push_namespace<NR, N>(&mut self, _name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        //TODO?
    }

    fn pop_namespace(&mut self, _gadget_name: Option<String>) {
        //TODO?
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        circuit::SimpleFloorPlanner,
        dev::ir::Ir,
        plonk::{Circuit, ConstraintSystem},
        poly::Rotation,
    };
    use ff::Field;
    use pasta_curves::pallas;

    #[derive(Copy, Clone)]
    struct MyConfig {}

    #[derive(Clone, Default)]
    struct MyCircuit {}

    impl<F: Field> Circuit<F> for MyCircuit {
        type Config = MyConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let a = meta.advice_column();
            let b = meta.advice_column();
            let c = meta.advice_column();
            let f = meta.fixed_column();
            let q1 = meta.selector();
            let q2 = meta.selector();

            meta.create_gate("Trial", |meta| {
                let a = meta.query_advice(a, Rotation::cur());
                let b = meta.query_advice(b, Rotation::cur());
                let c = meta.query_advice(c, Rotation::cur());
                let q1 = meta.query_selector(q1);

                Some(("trial constraint1", q1 * ((a + b) - c)))
            });

            meta.create_gate("Trial2", |meta| {
                let a = meta.query_advice(a, Rotation::cur());
                let b = meta.query_advice(b, Rotation::cur());
                let q2 = meta.query_selector(q2);

                Some(("trial constraint2", q2 * (a + b)))
            });

            meta.create_gate("Trial3", |meta| {
                let a = meta.query_advice(a, Rotation::next());
                let b = meta.query_advice(b, Rotation::cur());
                let f = meta.query_fixed(f, Rotation::prev());
                let q1 = meta.query_selector(q1);
                let q2 = meta.query_selector(q2);

                vec![q1 * (a.clone() * (a + b.clone())), q2 * (b + f)]
            });

            MyConfig {}
        }

        fn synthesize(
            &self,
            config: Self::Config,
            layouter: impl crate::circuit::Layouter<F>,
        ) -> Result<(), crate::plonk::Error> {
            Ok(())
        }
    }

    #[test]
    fn test1() {
        let mut cs = ConstraintSystem::<pallas::Base>::default();
        let _ = MyCircuit::configure(&mut cs);
        let mut ir = Ir::new(2, cs.num_fixed_columns, cs.num_selectors);
        let gates = ir.collect_gates(cs);
        for gate in gates {
            println!("{}", gate);
        }
    }
}
