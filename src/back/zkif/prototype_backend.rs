use std::fmt;
use zkinterface::{
    owned::{circuit::CircuitOwned, variables::VariablesOwned, keyvalue::KeyValueOwned, command::CommandOwned},
    statement::{StatementBuilder, Store, FileStore},
    Result,
};
use zkinterface_libsnark::gadgetlib::call_gadget_cb;

// WireId is an handle to reference a wire in the backend.
#[derive(Copy, Clone, PartialEq)]
pub struct WireId(pub usize); // or wid.

pub type ZkifId = u64; // or zid.

pub type PackedValue = [u64; 4];

// WireRepr holds one or several equivalent representations of a wire.
pub struct WireRepr {
    pub packed_zid: Option<ZkifId>,
    pub bit_zids: Vec<ZkifId>,
    pub one_hot_zids: Vec<ZkifId>,
}

// Backend centralizes all wires, representations, and basic components.
// Create new wires with new_wire.
// Push components with push_*.
// Access wire representations with get_repr_*.
pub struct PrototypeBackend {
    wire_reprs: Vec<WireRepr>,

    pub stmt: StatementBuilder<FileStore>,

    pub cost_est: CostEstimator,
}

impl PrototypeBackend {
    pub fn new(stmt: StatementBuilder<FileStore>) -> PrototypeBackend {
        PrototypeBackend {
            // Allocate the wire for constant one (zkif_id=0).
            wire_reprs: vec![WireRepr { packed_zid: Some(0), bit_zids: vec![], one_hot_zids: vec![] }],
            stmt,
            cost_est: CostEstimator {
                cost: 0,
                last_printed_cost: 0,
            },
        }
    }
}


// Wire representations in zkInterface.
impl PrototypeBackend {
    pub fn wire_one(&self) -> WireId { WireId(0) }

    pub fn wire_constant(&self, value: PackedValue) -> WireId { WireId(0) } // TODO: represent constants.

    pub fn new_wire(&mut self) -> WireId {
        self.wire_reprs.push(WireRepr { packed_zid: None, bit_zids: vec![], one_hot_zids: vec![] });
        WireId(self.wire_reprs.len() - 1)
    }

    pub fn new_wire_from_packed(&mut self, zid: ZkifId) -> WireId {
        self.wire_reprs.push(WireRepr { packed_zid: Some(zid), bit_zids: vec![], one_hot_zids: vec![] });
        WireId(self.wire_reprs.len() - 1)
    }

    pub fn represent_as_field(&mut self, wid: WireId) -> ZkifId {
        let wire = &mut self.wire_reprs[wid.0];
        match wire.packed_zid {
            Some(zid) => zid,
            None => {
                // Allocate a field variable.
                let zid = self.stmt.vars.allocate();
                wire.packed_zid = Some(zid);
                self.cost_est.cost += 1 + 16; // Word size, boolean-ness.
                // TODO: if other representations exists, enforce equality.
                zid
            }
        }
    }

    pub fn represent_as_bits(&mut self, wid: WireId) -> &[ZkifId] {
        let num_bits = 16;
        let wire = &mut self.wire_reprs[wid.0];
        if wire.bit_zids.len() == 0 {
            // Allocate bit variables.
            wire.bit_zids = self.stmt.vars.allocate_many(num_bits);

            self.cost_est.cost += 1 + num_bits;
            // TODO: enforce boolean-ness.
            // TODO: if other representations exists, enforce equality.
        }
        return &wire.bit_zids;
    }

    pub fn represent_as_one_hot(&mut self, wid: WireId) -> &[ZkifId] {
        let num_values = 32;
        let wire = &mut self.wire_reprs[wid.0];
        if wire.one_hot_zids.len() == 0 {
            // Allocate one-hot variables.
            wire.one_hot_zids = self.stmt.vars.allocate_many(num_values);

            self.cost_est.cost += 1 + num_values;
            // TODO: enforce one-hot-ness.
            // TODO: if other representations exists, enforce equality.
        }
        return &wire.one_hot_zids;
    }
}

pub struct CostEstimator {
    pub cost: usize,
    last_printed_cost: usize,
}

impl CostEstimator {
    pub fn print_cost(&mut self) {
        use colored::Colorize;
        println!("{}", format!("Cost of the above: {}", self.cost - self.last_printed_cost).yellow().italic());
        self.last_printed_cost = self.cost;
    }
}


impl fmt::Debug for WireId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        super::debug::write_wire_name(self.0, f)
        //write!(f, "&{:3}", self.0.to_string().blue())
    }
}
