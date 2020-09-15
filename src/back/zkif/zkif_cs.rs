use std::path::Path;

use zkinterface::{
    ConstraintSystemOwned, WitnessOwned, VariablesOwned, CircuitOwned, KeyValueOwned,
    statement::{StatementBuilder, FileStore, GadgetCallbacks, Store},
};
use zkinterface_bellman::{
    bellman::{ConstraintSystem, Variable, Index, LinearCombination, SynthesisError},
    ff::{ScalarEngine, PrimeField, PrimeFieldRepr, Field},
    sapling_crypto::circuit::boolean::{AllocatedBit, Boolean},
    pairing::bls12_381::Bls12,
    export::to_zkif_constraint,
};
use super::int64::Int64;
use super::num;

// TODO: template with trait ScalarEngine.
pub type En = Bls12;
pub type LC = LinearCombination<En>;
pub type Num = num::Num<En>;
pub type Fr = <En as ScalarEngine>::Fr;
pub type _FrRepr = <Fr as PrimeField>::Repr;


pub struct ZkifCS {
    stmt: StatementBuilder<FileStore>,
    constraints: ConstraintSystemOwned,
    proving: bool,
    witness: Vec<u8>,
}

impl ZkifCS {
    /// Must call finish() to finalize the files in the workspace.
    pub fn new(workspace: impl AsRef<Path>, proving: bool) -> ZkifCS {
        let store = FileStore::new(workspace, true, true, false).unwrap();
        let stmt = StatementBuilder::new(store);

        ZkifCS {
            stmt,
            constraints: ConstraintSystemOwned { constraints: vec![] },
            proving,
            witness: vec![],
        }
    }

    pub fn finish(mut self) {
        let mut msg = Vec::<u8>::new();
        self.constraints.write_into(&mut msg).unwrap();
        self.stmt.receive_constraints(&msg).unwrap();

        if self.proving {
            let variable_ids = (1..self.stmt.vars.free_variable_id).collect();
            let wit = WitnessOwned {
                assigned_variables: VariablesOwned {
                    variable_ids,
                    values: Some(self.witness.clone()),
                }
            };
            let mut msg = Vec::<u8>::new();
            wit.write_into(&mut msg).unwrap();
            self.stmt.receive_witness(&msg).unwrap();
        }

        let mut fr = <En as ScalarEngine>::Fr::one();
        fr.negate();
        let mut field_maximum = Vec::<u8>::new();
        fr.into_repr().write_le(&mut field_maximum).unwrap();

        let statement = CircuitOwned {
            connections: VariablesOwned {
                variable_ids: vec![],
                values: Some(vec![]),
            },
            free_variable_id: self.stmt.vars.free_variable_id,
            field_maximum: Some(field_maximum),
            configuration: Some(vec![
                KeyValueOwned {
                    key: "function".to_string(),
                    text: Some("witness-checker.test.tinyram".to_string()),
                    data: None,
                    number: 0,
                }]),
        };
        self.stmt.store.push_main(&statement).unwrap();
    }
}

impl ConstraintSystem<En> for ZkifCS {
    type Root = Self;

    fn alloc<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<Fr, SynthesisError>,
              A: FnOnce() -> AR, AR: Into<String>
    {
        let zkid = self.stmt.vars.allocate();
        if self.proving {
            let fr = f()?;
            fr.into_repr().write_le(&mut self.witness)?;
        }
        Ok(Variable::new_unchecked(Index::Aux(zkid as usize)))
    }

    fn alloc_input<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<Fr, SynthesisError>,
              A: FnOnce() -> AR, AR: Into<String>
    {
        ConstraintSystem::<En>::alloc(self, annotation, f)
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, annotation: A, a: LA, b: LB, c: LC)
        where A: FnOnce() -> AR, AR: Into<String>,
              LA: FnOnce(LinearCombination<En>) -> LinearCombination<En>,
              LB: FnOnce(LinearCombination<En>) -> LinearCombination<En>,
              LC: FnOnce(LinearCombination<En>) -> LinearCombination<En>
    {
        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());

        let co = to_zkif_constraint(a, b, c);
        self.constraints.constraints.push(co);
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N) where NR: Into<String>, N: FnOnce() -> NR {}

    fn pop_namespace(&mut self) {}

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

pub fn fr_from_unsigned<Fr: PrimeField>(val: u64) -> Fr {
    Fr::from_repr(<Fr::Repr as From<u64>>::from(val)).unwrap()
}

pub fn fr_from_signed<Fr: PrimeField>(val: i64) -> Fr {
    if val >= 0 {
        fr_from_unsigned(val as u64)
    } else {
        let mut f: Fr = fr_from_unsigned((-val) as u64);
        f.negate();
        f
    }
}