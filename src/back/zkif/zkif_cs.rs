use zkinterface::statement::{StatementBuilder, FileStore, GadgetCallbacks, Store};
use zkinterface_bellman::{
    bellman::{ConstraintSystem, Variable, Index, LinearCombination, SynthesisError},
    ff::ScalarEngine,
    sapling_crypto::circuit::{
        boolean::{AllocatedBit, Boolean},
    },
    pairing::bls12_381::Bls12,
};
use crate::back::zkif::uint32::UInt32;
use zkinterface::{ConstraintSystemOwned, WitnessOwned, VariablesOwned, CircuitOwned, KeyValueOwned};
use zkinterface_bellman::export::to_zkif_constraint;
use zkinterface_bellman::ff::{PrimeField, PrimeFieldRepr, Field};
use std::path::Path;
use super::num;
use crate::back::zkif::int::int_into_num;

// TODO: template with trait ScalarEngine.
pub type En = Bls12;
pub type LC = LinearCombination<En>;
pub type Num = num::Num<En>;
pub type Fr = <En as ScalarEngine>::Fr;
pub type FrRepr = <Fr as PrimeField>::Repr;

// WireId is an handle to reference a wire in the backend.
#[derive(Copy, Clone, PartialEq)]
pub struct WireId(pub usize); // or wid.

//pub type ZkifId = u64; // or zid.

// WireRepr holds one or several equivalent representations of a wire.
#[derive(Default)]
pub struct WireRepr {
    pub bl_boolean: Option<Boolean>,
    pub bl_num: Option<Num>,
    pub bl_uint32: Option<UInt32>,
    //pub packed_zid: Option<ZkifId>,
    //pub bit_zids: Vec<ZkifId>,
    //pub one_hot_zids: Vec<ZkifId>,
}

pub struct ZkifCS {
    stmt: StatementBuilder<FileStore>,
    constraints: ConstraintSystemOwned,
    proving: bool,
    witness: Vec<u8>,
}

impl ZkifCS {
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
}

impl Drop for ZkifCS {
    fn drop(&mut self) {
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


pub fn fr_from_unsigned(val: u64) -> Fr {
    Fr::from_repr(FrRepr::from(val)).unwrap()
}

pub fn fr_from_signed(val: i64) -> Fr {
    if val >= 0 {
        fr_from_unsigned(val as u64)
    } else {
        let mut f = fr_from_unsigned((-val) as u64);
        f.negate();
        f
    }
}