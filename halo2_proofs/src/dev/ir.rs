//! IR for Plonk.

// Integers are represented as big-endian byte vectors
// metadata: {"name": "MyCircuit", ...}
// config: {"n_rows": 5, "n_instance": 2, "n_advice: 10", "n_fixed": 4}
// constraints: [(F, 0, 1) * ((A, 1, 0) + (I, 0, -1)), ... ]
// fixed: [[1,2,3], [4,5,6], ...]
// copies: [((I,0,0), (A,1,2)), ...]
// halo2.gates: [ {name: "gate name", constraints: [{0 : "contraint 0"}, {3: "constraint 3"}]}]
// halo2.lookups: [ {0: lookup_maps} ]
// lookup_maps: [{0: ("input poly", "table_poly")}]

use super::util;
use crate::circuit::Value;
use crate::plonk::{
    Advice, Any, Assigned, Assignment, Circuit, Column, ConstraintSystem, Error, Fixed,
    FloorPlanner, Instance, Selector,
};
use crate::poly::Rotation;
use ff::{Field, PrimeField};
use pasta_curves::arithmetic::FieldExt;
use serde::{Serialize, Serializer};
use std::collections::HashMap;
use std::fmt;
use std::io;
use std::ops::Index;
use std::os::unix::prelude::FileExt;
use std::path::Ancestors;
use std::slice::SliceIndex;

#[derive(Debug, Serialize, Copy, Clone)]
pub enum ColumnType {
    Instance,
    Advice,
    Fixed,
}

#[derive(Debug, Serialize, Copy, Clone)]
pub struct Variable {
    column_type: ColumnType,
    index: usize,
    offset: i32,
}

// Polynomial with scalars represented as Vec<u8>
#[derive(Serialize, Clone)]
pub enum Polynomial<F: FieldExt> {
    Var(Variable),
    #[serde(bound(serialize = "F::Repr: Serialize"))]
    Scalar(F::Repr),
    #[serde(bound(serialize = "F::Repr: Serialize"))]
    Neg(Box<Polynomial<F>>),
    #[serde(bound(serialize = "F::Repr: Serialize"))]
    Add(Box<Polynomial<F>>, Box<Polynomial<F>>),
    #[serde(bound(serialize = "F::Repr: Serialize"))]
    Mul(Box<Polynomial<F>>, Box<Polynomial<F>>),
}

pub struct Constraint<F: FieldExt> {
    name: &'static str,
    expression: Polynomial<F>,
}

pub struct Gate<F: FieldExt> {
    name: &'static str,
    constraints: Vec<Constraint<F>>,
}
#[derive(Serialize, Debug)]
pub struct Lookup<F: FieldExt> {
    index: usize,
    #[serde(bound(serialize = "F::Repr: Serialize"))]
    mappings: Vec<LookupMap<F>>,
}

#[derive(Serialize, Debug)]
pub struct LookupMap<F: FieldExt> {
    index: usize,
    #[serde(bound(serialize = "F::Repr: Serialize"))]
    input: Polynomial<F>,
    #[serde(bound(serialize = "F::Repr: Serialize"))]
    table: Polynomial<F>,
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.column_type {
            ColumnType::Advice => write!(f, "A{{{},{}}}", self.index, self.offset),
            ColumnType::Fixed => write!(f, "F{{{},{}}}", self.index, self.offset),
            ColumnType::Instance => write!(f, "I{{{},{}}}", self.index, self.offset),
        }
    }
}

impl<F: FieldExt> fmt::Display for Polynomial<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var(v) => write!(f, "{}", v),
            Self::Scalar(v) => write!(f, "{}", &util::format_value(F::from_repr(*v).unwrap())),
            Self::Neg(x) => write!(f, "-{}", x),
            Self::Add(x, y) => match &**y {
                Self::Neg(y) => write!(f, "({} - {})", x, y),
                _ => write!(f, "({} + {})", x, y),
            },
            Self::Mul(x, y) => write!(f, "({} * {})", x, y),
        }
    }
}

impl<F: FieldExt> fmt::Debug for Polynomial<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl<F: FieldExt> fmt::Display for Constraint<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.name.is_empty() {
            write!(f, "{}", self.expression)
        } else {
            write!(f, "{}: {}", self.name, self.expression)
        }
    }
}

impl<F: FieldExt> fmt::Display for Gate<F> {
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

impl<F: FieldExt> fmt::Display for Lookup<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: [", self.index)?;
        for m in &self.mappings {
            write!(f, "{}", m)?;
        }
        write!(f, "]")
    }
}

impl<F: FieldExt> fmt::Display for LookupMap<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: (", self.index)?;
        write!(f, "{}, ", self.input)?;
        write!(f, "{})", self.table)
    }
}

#[derive(Debug, Serialize)]
struct IrConfig {
    //   field_prime: F::Repr, // TODO: Figure out how to extract the field prime -- wierdly difficult
    n_rows: usize,
    n_instance: usize,
    n_advice: usize,
    n_fixed: usize,
}
#[derive(Serialize, Debug)]
struct Ir<F: FieldExt> {
    config: IrConfig,
    #[serde(bound(serialize = "Polynomial<F>: Serialize"))]
    constraints: Vec<Polynomial<F>>,
    #[serde(bound(serialize = "Lookup<F>: Serialize"))]
    lookups: Vec<Lookup<F>>,
    #[serde(bound(serialize = "F::Repr: Serialize"))]
    fixed: Vec<Vec<F::Repr>>,
}

impl<F: FieldExt> Ir<F>
where
    F::Repr: Serialize,
{
    fn new(
        cs: &ConstraintSystem<F>,
        num_rows: usize,
        gates: Vec<Gate<F>>,
        lookups: Vec<Lookup<F>>,
        fixed: Vec<Vec<F::Repr>>,
    ) -> Self {
        Self {
            config: IrConfig {
                n_rows: num_rows,
                n_instance: cs.num_instance_columns,
                n_advice: cs.num_advice_columns,
                n_fixed: cs.num_fixed_columns,
            },
            constraints: gates
                .iter()
                .flat_map(|g| g.constraints.iter().map(|c| c.expression.clone()))
                .collect(),
            lookups,
            fixed,
        }
    }
}
struct IrWriter<F: FieldExt> {
    k: u32,
    num_rows: usize,
    fixed: Vec<Vec<F::Repr>>,
    selectors: Vec<Vec<bool>>,
    equality: Vec<(Column<Any>, usize, Column<Any>, usize)>,
    // Start of selector fixed columns
    selector_index: usize,
}

impl<F: FieldExt> IrWriter<F>
where
    F::Repr: Serialize,
{
    fn new(k: u32, num_fixed: usize, num_selectors: usize) -> Self {
        let num_rows = 1 << k;
        Self {
            k,
            num_rows,
            fixed: vec![vec![F::Repr::default(); num_rows]; num_fixed],
            selectors: vec![vec![false; num_rows]; num_selectors],
            equality: vec![],
            selector_index: num_fixed,
        }
    }

    fn collect_gates(&self, cs: &ConstraintSystem<F>) -> Vec<Gate<F>> {
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
                            &|s| Polynomial::Scalar(s.to_repr()),
                            &|selector| {
                                Polynomial::Var(Variable {
                                    column_type: ColumnType::Fixed,
                                    index: self.selector_index + selector.0,
                                    offset: 0,
                                })
                            },
                            &|_, column, rotation| {
                                Polynomial::Var(Variable {
                                    column_type: ColumnType::Fixed,
                                    index: column,
                                    offset: rotation.0,
                                })
                            },
                            &|_, column, rotation| {
                                Polynomial::Var(Variable {
                                    column_type: ColumnType::Advice,
                                    index: column,
                                    offset: rotation.0,
                                })
                            },
                            &|_, column, rotation| {
                                Polynomial::Var(Variable {
                                    column_type: ColumnType::Instance,
                                    index: column,
                                    offset: rotation.0,
                                })
                            },
                            &|x| Polynomial::Neg(Box::new(x)),
                            &|x, y| Polynomial::Add(Box::new(x), Box::new(y)),
                            &|x, y| Polynomial::Mul(Box::new(x), Box::new(y)),
                            &|a, s| {
                                Polynomial::Mul(
                                    Box::new(Polynomial::Scalar(s.to_repr())),
                                    Box::new(a),
                                )
                            },
                        ),
                    })
                    .collect(),
            })
            .collect()
    }

    fn collect_lookup(&mut self, cs: &ConstraintSystem<F>) -> Vec<Lookup<F>> {
        cs.lookups
            .iter()
            .map(|lookup| Lookup {
                index: 0,
                mappings: lookup
                    .input_expressions
                    .iter()
                    .zip(lookup.table_expressions.iter())
                    .enumerate()
                    .map(|(index, (input, table))| LookupMap {
                        index,
                        input: input.evaluate(
                            &|s| Polynomial::Scalar(s.to_repr()),
                            &|selector| {
                                Polynomial::Var(Variable {
                                    column_type: ColumnType::Fixed,
                                    index: self.selector_index + selector.0,
                                    offset: 0,
                                })
                            },
                            &|_, column, rotation| {
                                Polynomial::Var(Variable {
                                    column_type: ColumnType::Fixed,
                                    index: column,
                                    offset: rotation.0,
                                })
                            },
                            &|_, column, rotation| {
                                Polynomial::Var(Variable {
                                    column_type: ColumnType::Advice,
                                    index: column,
                                    offset: rotation.0,
                                })
                            },
                            &|_, column, rotation| {
                                Polynomial::Var(Variable {
                                    column_type: ColumnType::Instance,
                                    index: column,
                                    offset: rotation.0,
                                })
                            },
                            &|x| Polynomial::Neg(Box::new(x)),
                            &|x, y| Polynomial::Add(Box::new(x), Box::new(y)),
                            &|x, y| Polynomial::Mul(Box::new(x), Box::new(y)),
                            &|a, s| {
                                Polynomial::Mul(
                                    Box::new(Polynomial::Scalar(s.to_repr())),
                                    Box::new(a),
                                )
                            },
                        ),
                        table: table.evaluate(
                            &|s| Polynomial::Scalar(s.to_repr()),
                            &|selector| {
                                Polynomial::Var(Variable {
                                    column_type: ColumnType::Fixed,
                                    index: self.selector_index + selector.0,
                                    offset: 0,
                                })
                            },
                            &|_, column, rotation| {
                                Polynomial::Var(Variable {
                                    column_type: ColumnType::Fixed,
                                    index: column,
                                    offset: rotation.0,
                                })
                            },
                            &|_, column, rotation| {
                                Polynomial::Var(Variable {
                                    column_type: ColumnType::Advice,
                                    index: column,
                                    offset: rotation.0,
                                })
                            },
                            &|_, column, rotation| {
                                Polynomial::Var(Variable {
                                    column_type: ColumnType::Instance,
                                    index: column,
                                    offset: rotation.0,
                                })
                            },
                            &|x| Polynomial::Neg(Box::new(x)),
                            &|x, y| Polynomial::Add(Box::new(x), Box::new(y)),
                            &|x, y| Polynomial::Mul(Box::new(x), Box::new(y)),
                            &|a, s| {
                                Polynomial::Mul(
                                    Box::new(Polynomial::Scalar(s.to_repr())),
                                    Box::new(a),
                                )
                            },
                        ),
                    })
                    .collect(),
            })
            .collect()
    }
}

impl<F: FieldExt> Assignment<F> for IrWriter<F> {
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
        *cell = to().into_field().evaluate().assign()?.to_repr();
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

/// TODO: error handling
pub fn write<F, ConcreteCircuit, Writer>(
    k: u32,
    circuit: &ConcreteCircuit,
    compress: bool,
    outfile: Writer,
) where
    F: FieldExt,
    F::Repr: Serialize,
    ConcreteCircuit: Circuit<F>,
    Writer: io::Write,
{
    let mut cs = ConstraintSystem::default();
    let config = ConcreteCircuit::configure(&mut cs);
    let mut ir = IrWriter::new(k, cs.num_fixed_columns, cs.num_selectors);
    ConcreteCircuit::FloorPlanner::synthesize(&mut ir, circuit, config, cs.constants.clone())
        .unwrap();

    if compress {
        let (cs_compressed, selector_polys) = cs.compress_selectors(ir.selectors.clone());
        assert!(cs_compressed.num_fixed_columns == ir.selector_index + selector_polys.len());
        cs = cs_compressed;
        ir.fixed.extend(
            selector_polys
                .iter()
                .map(|v| v.iter().map(|x| x.to_repr()).collect()),
        )
    } else {
        ir.fixed.extend(
            ir.selectors
                .iter()
                .map(|r| r.iter().map(|&s| F::from(s).to_repr()).collect())
                .collect::<Vec<_>>(),
        );
    }
    let gates = ir.collect_gates(&cs);
    let lookups = ir.collect_lookup(&cs);
    let irdata = Ir::new(&cs, ir.num_rows, gates, lookups, ir.fixed);
    serde_json::to_writer(outfile, &irdata).unwrap(); // TODO: allow toggle between JSON and CBOR?
}

#[cfg(test)]
mod tests {
    use crate::{
        arithmetic::FieldExt,
        circuit::{SimpleFloorPlanner, Value},
        dev::ir::write,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Fixed, Selector, TableColumn},
        poly::Rotation,
    };
    use ff::Field;
    use pasta_curves::pallas;
    use proptest::sample::Select;

    #[derive(Copy, Clone)]
    struct MyConfig {
        _a: Column<Advice>,
        _b: Column<Advice>,
        _c: Column<Advice>,
        f: Column<Fixed>,
        q1: Selector,
        q2: Selector,
        q3: Selector,
        t1: TableColumn,
    }

    #[derive(Clone, Default)]
    struct MyCircuit {}

    impl<F: FieldExt> Circuit<F> for MyCircuit {
        type Config = MyConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let _a = meta.advice_column();
            let _b = meta.advice_column();
            let _c = meta.advice_column();
            let f = meta.fixed_column();
            let q1 = meta.selector();
            let q2 = meta.selector();
            let q3 = meta.complex_selector();
            let t1 = meta.lookup_table_column();

            meta.create_gate("Trial", |meta| {
                let a = meta.query_advice(_a, Rotation::cur());
                let b = meta.query_advice(_b, Rotation::cur());
                let c = meta.query_advice(_c, Rotation::cur());
                let q1 = meta.query_selector(q1);

                Some(("trial constraint1", q1 * ((a + b) - c)))
            });

            meta.create_gate("Trial2", |meta| {
                let a = meta.query_advice(_a, Rotation::cur());
                let b = meta.query_advice(_b, Rotation::cur());
                let q2 = meta.query_selector(q2);

                Some(("trial constraint2", q2 * (a + b)))
            });

            meta.create_gate("Trial3", |meta| {
                let a = meta.query_advice(_a, Rotation::next());
                let b = meta.query_advice(_b, Rotation::cur());
                let f = meta.query_fixed(f, Rotation::prev());
                let q1 = meta.query_selector(q1);
                let q2 = meta.query_selector(q2);

                vec![q1 * (a.clone() * (a + b.clone())), q2 * (b + f)]
            });

            // lookup
            meta.lookup(|meta| {
                let q3 = meta.query_selector(q3);
                let a = meta.query_advice(_a, Rotation::cur());
                let b = meta.query_advice(_b, Rotation::cur());
                vec![(q3 * (a + b), t1)]
            });

            MyConfig {
                _a,
                _b,
                _c,
                f,
                q1,
                q2,
                q3,
                t1,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl crate::circuit::Layouter<F>,
        ) -> Result<(), crate::plonk::Error> {
            layouter.assign_table(
                || "table1",
                |mut table| {
                    table.assign_cell(|| "cell1", config.t1, 0, || Value::known(F::from(42)))
                },
            )?;
            layouter.assign_region(
                || "region1",
                |mut region| {
                    config.q1.enable(&mut region, 0)?;
                    config.q2.enable(&mut region, 1)?;
                    config.q3.enable(&mut region, 2)?;
                    region.assign_fixed(|| "f1", config.f, 4, || Value::known(F::from(42)))?;
                    Ok(())
                },
            )
        }
    }

    #[test]
    fn test1() {
        write::<pallas::Base, MyCircuit, std::io::Stdout>(
            4,
            &MyCircuit::default(),
            true,
            std::io::stdout(),
        )
    }
}
