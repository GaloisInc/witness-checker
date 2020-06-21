use std::fmt;

// TODO: Use types and opcodes from the rest of the package.
pub type OpLabel = usize;

#[derive(Copy, Clone)]
pub struct WireId(pub usize); // or wid.

type ZkifId = u64; // or zid.

struct WireRepr {
    packed_zid: Option<ZkifId>,
    bit_zids: Vec<ZkifId>,
}

pub struct Backend {
    wire_reprs: Vec<WireRepr>,
    free_zid: ZkifId,

    pub cost: usize,
    last_printed_cost: usize,
}

impl Backend {
    pub fn new() -> Backend { Backend { free_zid: 1, wire_reprs: vec![], cost: 0, last_printed_cost: 0 } }

    pub fn new_wire(&mut self) -> WireId {
        self.wire_reprs.push(WireRepr { packed_zid: None, bit_zids: vec![] });
        return WireId(self.wire_reprs.len() - 1);
    }

    pub fn true_wire(&self) -> WireId { WireId(0) }

    pub fn print_cost(&mut self) {
        //println!("{}", format!("Cost of the above: {}", self.cost - self.last_printed_cost).yellow().italic());
        self.last_printed_cost = self.cost;
    }
}

// Core execution units.
impl Backend {
    pub fn push_alu_op(&mut self, opcode: OpLabel, regval0: WireId, regval1: WireId, regval2: WireId) -> (WireId, WireId) {
        // TODO: use the implementation for the given opcode.
        let new_reg = self.new_wire();
        let new_flag = self.new_wire();
        self.cost += 30;
        println!("{:?}\t= alu_op_{}( {:?}, {:?}, {:?})", (new_reg, new_flag), opcode, regval0, regval1, regval2);
        return (new_reg, new_flag);
    }

    pub fn push_flow_op(&mut self, opcode: OpLabel, flag: WireId, pc: WireId, regval: WireId) -> WireId {
        // TODO: use the implementation for the given opcode.
        let new_pc = self.new_wire();
        self.cost += 4;
        println!("{:?}\t= flow_op_{}( {:?}, {:?}, {:?} )", new_pc, opcode, pc, flag, regval);
        return new_pc;
    }

    // new wire = inputs[index]
    pub fn push_demux(&mut self, inputs: &[WireId], index: WireId) -> WireId {
        // TODO: use secret index.
        let regout = self.new_wire();
        self.cost += 1 + inputs.len();
        println!("{:?}\t= demux selects {:?} from {:?}", regout, index, inputs);
        return regout;
    }

    // new tuple = input_tuples[index]
    pub fn push_demux_tuple(&mut self, inputs: &[(WireId, WireId)], index: WireId) -> (WireId, WireId) {
        // TODO: use secret index.
        let regout = (self.new_wire(), self.new_wire());
        self.cost += 1 + inputs.len();
        println!("{:?}\t= demux selects {:?} from {:?}", regout, index, inputs);
        return regout;
    }

    pub fn push_decode_op_type(&mut self, opcode: WireId) -> WireId {
        // TODO: decode.
        let is_flow = self.new_wire();
        return is_flow;
    }

    // regs[index] = new wire equal to new_value.
    // regs[i] = new wire equal to regs[i], for i != index.
    pub fn push_update(&mut self, regs: &mut [WireId], index: WireId, new_value: WireId) {
        for i in 0..regs.len() {
            // TODO: condition on secret index.
            regs[i] = self.new_wire();
        }
        self.cost += 1 + regs.len();
        println!("regs[{:?}]\t= {:?} in new registers {:?}", index, new_value, regs);
    }
}


// Wire representations in zkInterface.
impl Backend {
    fn get_field_repr(&mut self, wid: WireId) -> ZkifId {
        let wire = &mut self.wire_reprs[wid.0];
        match wire.packed_zid {
            Some(zid) => zid,
            None => {
                let zid = self.free_zid;
                self.free_zid += 1;
                wire.packed_zid = Some(zid);
                self.cost += 1 + 16; // Word size, boolean-ness.
                // TODO: if bits repr exists, enforce equality.
                zid
            }
        }
    }

    fn get_bit_repr(&mut self, wid: WireId) -> &[ZkifId] {
        let wire = &mut self.wire_reprs[wid.0];
        if wire.bit_zids.len() == 0 {
            let width = 16;
            wire.bit_zids.resize(width, 0);
            for bit_i in 0..width {
                wire.bit_zids[bit_i] = self.free_zid + bit_i as u64;
            }
            self.free_zid += width as u64;
            self.cost += 1 + width;
            // TODO: enforce boolean-ness.
            // TODO: if field repr exists, enforce equality.
        }
        return &wire.bit_zids;
    }
}
