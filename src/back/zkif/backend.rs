use std::fmt;

// TODO: Use types and opcodes from the rest of the package.
pub type OpLabel = usize;

// WireId is an handle to reference a wire in the backend.
#[derive(Copy, Clone)]
pub struct WireId(usize); // or wid.

type ZkifId = u64; // or zid.

pub type PackedValue = [u64; 4];

// WireRepr holds one or several equivalent representations of a wire.
struct WireRepr {
    packed_zid: Option<ZkifId>,
    bit_zids: Vec<ZkifId>,
    one_hot_zids: Vec<ZkifId>,
}

// Backend centralizes all wires, representations, and basic components.
// Create new wires with new_wire.
// Push components with push_*.
// Access wire representations with get_repr_*.
pub struct Backend {
    wire_reprs: Vec<WireRepr>,
    free_zid: ZkifId,

    pub cost_est: CostEstimator,
}

impl Backend {
    pub fn new() -> Backend {
        Backend {
            // Allocate the wire for constant one (zkif_id=0).
            wire_reprs: vec![WireRepr { packed_zid: Some(0), bit_zids: vec![], one_hot_zids: vec![] }],
            free_zid: 1,
            cost_est: CostEstimator {
                cost: 0,
                last_printed_cost: 0,
            },
        }
    }

    pub fn new_wire(&mut self) -> WireId {
        self.wire_reprs.push(WireRepr { packed_zid: None, bit_zids: vec![], one_hot_zids: vec![] });
        WireId(self.wire_reprs.len() - 1)
    }

    pub fn wire_one(&self) -> WireId { WireId(0) }

    pub fn wire_constant(&self, value: PackedValue) -> WireId { WireId(0) } // TODO: represent constants.
}


// Core execution units.
impl Backend {
    // Add a stateless Arithmetic & Logic Unit:
    //   new result and flag = operation( arg0, arg1, arg2 )
    pub fn push_alu_op(&mut self, opcode: OpLabel, arg0: WireId, arg1: WireId, arg2: WireId) -> (WireId, WireId) {
        let _ = self.represent_as_bits(arg0);
        let _ = self.represent_as_bits(arg1);
        let _ = self.represent_as_bits(arg2);

        // TODO: call the gadget for the given opcode using the wire representations.
        self.cost_est.cost += 30;
        let new_res = self.new_wire();
        let new_flag = self.new_wire();

        println!("{:?}\t= alu_op_{}( {:?}, {:?}, {:?})", (new_res, new_flag), opcode, arg0, arg1, arg2);
        return (new_res, new_flag);
    }

    // Add a stateless Flow Control Unit:
    //   new pc = operation( flag, pc, arg2 )
    pub fn push_flow_op(&mut self, opcode: OpLabel, flag: WireId, pc: WireId, arg2: WireId) -> WireId {
        let _ = self.represent_as_field(flag);
        let _ = self.represent_as_field(pc);
        let _ = self.represent_as_field(arg2);

        // TODO: call the gadget for the given opcode using the wire representations.
        self.cost_est.cost += 4;
        let new_pc = self.new_wire();

        println!("{:?}\t= flow_op_{}( {:?}, {:?}, {:?} )", new_pc, opcode, pc, flag, arg2);
        return new_pc;
    }

    // Select one of multiple inputs at a secret index:
    //   new wire = inputs[index]
    // Or 0 if out-of-range.
    pub fn push_muxer(&mut self, inputs: &[WireId], index: WireId) -> WireId {
        for w in inputs {
            let _ = self.represent_as_field(*w);
        }
        let _ = self.represent_as_one_hot(index);

        // TODO: call the muxer gadget.
        self.cost_est.cost += inputs.len();
        let mux_out = self.new_wire();

        println!("{:?}\t= muxer selects {:?} from {:?}", mux_out, index, inputs);
        return mux_out;
    }

    // Like push_muxer for pairs of wires accessed with the same secret index:
    //   new wire tuple = input_tuples[index]
    pub fn push_muxer_pair(&mut self, inputs: &[(WireId, WireId)], index: WireId) -> (WireId, WireId) {
        for (wa, wb) in inputs {
            let _ = self.represent_as_field(*wa);
            let _ = self.represent_as_field(*wb);
        }
        let _ = self.represent_as_one_hot(index);

        // TODO: call the muxer gadget.
        self.cost_est.cost += inputs.len() * 2;
        let mux_out = (self.new_wire(), self.new_wire());

        println!("{:?}\t= muxer selects {:?} from {:?}", mux_out, index, inputs);
        return mux_out;
    }

    // Update one of multiple registers at a secret index:
    //   registers[index] = new wire equal to new_value.
    // Unchanged registers are replaced by copies of their values:
    //   registers[i != index] = new wire equal to the old value.
    pub fn push_demuxer(&mut self, registers: &mut [WireId], index: WireId, new_value: WireId) {
        for w in &registers[..] {
            let _ = self.represent_as_field(*w);
        }
        let _ = self.represent_as_one_hot(index);
        let _ = self.represent_as_field(new_value);

        // TODO: call the demuxer gadget.
        self.cost_est.cost += registers.len();
        for i in 0..registers.len() {
            registers[i] = self.new_wire();
        }

        println!("regs[{:?}]\t= {:?} in new registers {:?}", index, new_value, registers);
    }
}


// Wire representations in zkInterface.
impl Backend {
    pub fn represent_as_field(&mut self, wid: WireId) -> ZkifId {
        let wire = &mut self.wire_reprs[wid.0];
        match wire.packed_zid {
            Some(zid) => zid,
            None => {
                // Allocate a field variable.
                let zid = self.free_zid;
                self.free_zid += 1;
                wire.packed_zid = Some(zid);
                self.cost_est.cost += 1 + 16; // Word size, boolean-ness.
                // TODO: if other representations exists, enforce equality.
                zid
            }
        }
    }

    pub fn represent_as_bits(&mut self, wid: WireId) -> &[ZkifId] {
        let width = 16;
        let wire = &mut self.wire_reprs[wid.0];
        if wire.bit_zids.len() == 0 {
            // Allocate bit variables.
            wire.bit_zids.resize(width, 0);
            for bit_i in 0..width {
                wire.bit_zids[bit_i] = self.free_zid + bit_i as u64;
            }
            self.free_zid += width as u64;
            self.cost_est.cost += 1 + width;
            // TODO: enforce boolean-ness.
            // TODO: if other representations exists, enforce equality.
        }
        return &wire.bit_zids;
    }

    pub fn represent_as_one_hot(&mut self, wid: WireId) -> &[ZkifId] {
        let width = 32;
        let wire = &mut self.wire_reprs[wid.0];
        if wire.one_hot_zids.len() == 0 {
            // Allocate one-hot variables.
            wire.one_hot_zids.resize(width, 0);
            for bit_i in 0..width {
                wire.one_hot_zids[bit_i] = self.free_zid + bit_i as u64;
            }
            self.free_zid += width as u64;
            self.cost_est.cost += 1 + width;
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
