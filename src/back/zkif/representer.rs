use zkinterface::statement::{StatementBuilder, FileStore};
use zkinterface_bellman::{
    bellman::{ConstraintSystem, Variable, Index, LinearCombination, SynthesisError},
    ff::ScalarEngine,
    sapling_crypto::circuit::boolean::{AllocatedBit, Boolean},
    pairing::bls12_381::Bls12,
};

// WireId is an handle to reference a wire in the backend.
#[derive(Copy, Clone, PartialEq)]
pub struct WireId(pub usize); // or wid.

pub type ZkifId = u64; // or zid.

// WireRepr holds one or several equivalent representations of a wire.
#[derive(Default)]
pub struct WireRepr {
    pub packed_zid: Option<ZkifId>,
    pub bit_zids: Vec<ZkifId>,
    pub one_hot_zids: Vec<ZkifId>,
    pub bl_boolean: Option<Boolean>,
}

pub struct WireRepresenter {
    stmt: StatementBuilder<FileStore>,
    pub wire_reprs: Vec<WireRepr>,
}

impl WireRepresenter {
    pub fn new() -> WireRepresenter {
        let out_path = "local/test_backend";
        let store = FileStore::new(out_path, true, true, true).unwrap();
        let stmt = StatementBuilder::new(store);

        WireRepresenter { stmt, wire_reprs: vec![] }
    }

    pub fn allocate_repr(&mut self) -> WireId {
        self.wire_reprs.push(WireRepr::default());
        WireId(self.wire_reprs.len() - 1)
    }

    pub fn wire_as_field(&mut self, wid: WireId) -> ZkifId {
        let repr = &mut self.wire_reprs[wid.0];
        match repr.packed_zid {
            Some(zid) => zid,
            None => {
                // Allocate a field variable.
                let zid = self.stmt.vars.allocate();
                repr.packed_zid = Some(zid);
                // TODO: if other representations exists, enforce equality.
                zid
            }
        }
    }

    pub fn set_bellman_boolean(&mut self, wid: WireId, b: Boolean) {
        self.wire_reprs[wid.0].bl_boolean = Some(b);
    }

    pub fn as_bellman_boolean(&mut self, wid: WireId) -> Boolean {
        let repr = &mut self.wire_reprs[wid.0];
        match &repr.bl_boolean {
            Some(b) => b.clone(),
            None => {
                // TODO: convert from other repr.
                Boolean::constant(false)
            }
        }
    }
}

// TODO: template with trait ScalarEngine.
pub type En = Bls12;

impl<E: ScalarEngine> ConstraintSystem<E> for WireRepresenter {
    type Root = Self;

    fn alloc<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>,
              A: FnOnce() -> AR, AR: Into<String>
    {
        let zid = self.stmt.vars.allocate();
        Ok(Variable::new_unchecked(Index::Aux(zid as usize)))
    }

    fn alloc_input<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>,
              A: FnOnce() -> AR, AR: Into<String>
    {
        ConstraintSystem::<E>::alloc(self, annotation, f)
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, annotation: A, a: LA, b: LB, c: LC)
        where A: FnOnce() -> AR, AR: Into<String>,
              LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>
    {
        eprintln!("Received a Bellman constraint: {}", annotation().into());
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N) where NR: Into<String>, N: FnOnce() -> NR {}

    fn pop_namespace(&mut self) {}

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}
