mod debug;

use std::fmt;
use colored::Colorize;
use std::collections::HashMap;

// TODO: Use actual types.
type OpLabel = usize;
type RegLabel = usize;

#[derive(Copy, Clone)]
pub struct WireId(usize); // or wid.

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

    pub fn print_cost(&mut self) {
        println!("{}", format!("Cost of the above: {}", self.cost - self.last_printed_cost).italic());
        self.last_printed_cost = self.cost;
    }
}

pub fn is_alu(opcode: OpLabel) -> bool {
    return opcode <= 12;
}

// Core execution units.
impl Backend {
    // result, flag = operation(arg0 arg1 arg2)
    pub fn push_operation(&mut self, opcode: OpLabel, regval0: WireId, regval1: WireId, regval2: WireId, pc: WireId, flag: WireId) -> (WireId, WireId, WireId) {
        let is_alu = false; // TODO
        if is_alu {
            let (res, new_flag) = self.push_alu_op(opcode, regval0, regval1, regval2);
            let new_pc = pc; // TODO: pc+1
            return (res, new_flag, new_pc);
        } else {
            let new_pc = self.push_flow_op(opcode, pc, flag);
            return (regval0, flag, new_pc);
        }
    }

    pub fn push_alu_op(&mut self, opcode: OpLabel, regval0: WireId, regval1: WireId, regval2: WireId) -> (WireId, WireId) {
        // TODO: use the implementation for the given opcode.
        let new_reg = self.new_wire();
        let new_flag = self.new_wire();
        self.cost += 30;
        println!("{:?}\t= operation_{}( {:?}, {:?}, {:?})", (new_reg, new_flag), opcode, regval0, regval1, regval2);
        return (new_reg, new_flag);
    }

    pub fn push_flow_op(&mut self, opcode: OpLabel, pc: WireId, flag: WireId) -> WireId {
        // TODO: use the implementation for the given opcode.
        let new_pc = self.new_wire();
        self.cost += 4;
        println!("{:?}\t= flow_op_{}( {:?}, {:?} )", new_pc, opcode, pc, flag);
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

    // new wire pair = input_pairs[index]
    pub fn push_demux_pair(&mut self, inputs: &[(WireId, WireId)], index: WireId) -> (WireId, WireId) {
        // TODO: use secret index.
        let regout = (self.new_wire(), self.new_wire());
        self.cost += 1 + inputs.len();
        println!("{:?}\t= demux selects {:?} from {:?}", regout, index, inputs);
        return regout;
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

pub struct FixedInstr {
    oplabel: OpLabel,
    reglabel0: RegLabel,
    reglabel1: RegLabel,
    reglabel2: RegLabel,
}

pub struct SecretInstr<'a> {
    possible_opcodes: &'a [OpLabel],
    opcode: WireId,
    reglabel0: WireId,
    reglabel1: WireId,
    reglabel2: WireId,
}

// CPU components. Compose and connect core components.
impl Backend {
    pub fn push_instr(&mut self, regs: &mut [WireId], instr: &FixedInstr) {
        println!("instruction operation_{}( {}, {}, {} )", instr.oplabel, instr.reglabel0, instr.reglabel1, instr.reglabel2);
        let (result, _flag) = self.push_alu_op(
            instr.oplabel,
            regs[instr.reglabel0],
            regs[instr.reglabel1],
            regs[instr.reglabel2]);
        regs[instr.reglabel0] = result;
        println!("registers[{}]\t= {:?}", instr.reglabel0, result);
        self.print_cost();
    }

    pub fn push_secret_instr(&mut self, regvals: &mut [WireId], instr: &SecretInstr) {
        println!("secret instruction {:?}( {:?}, {:?}, {:?} )", instr.opcode, instr.reglabel0, instr.reglabel1, instr.reglabel2);
        println!("// Pick the register inputs from all possible registers.");
        let regval0 = self.push_demux(regvals, instr.reglabel0);
        let regval1 = self.push_demux(regvals, instr.reglabel1);
        let regval2 = self.push_demux(regvals, instr.reglabel2);
        self.print_cost();

        println!("// Execute all possible operations.");
        let possible_results = instr.possible_opcodes.iter().map(|op|
            self.push_alu_op(*op, regval0, regval1, regval2)
        ).collect::<Vec<(WireId, WireId)>>();
        self.print_cost();

        println!("// Pick the result of the actual operation.");
        let result = self.push_demux_pair(&possible_results, instr.opcode);

        self.push_update(regvals, instr.reglabel0, result.0);
        self.print_cost();
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


pub struct Memory {
    ops: Vec<MemOp>,
    values: HashMap<PackedValue, PackedValue>,
    finished: bool,
}

enum MemOp {
    Store { addr: WireId, content: WireId },
    Load { addr: WireId, content: WireId },
}

type PackedValue = [u64; 4];

impl Memory {
    pub fn new() -> Memory {
        Memory { ops: vec![], values: HashMap::new(), finished: false }
    }
    pub fn finish(mut self, back: &mut Backend) {
        // TODO: store/load consistency check.
        self.finished = true;
    }

    pub fn store(&mut self, addr: WireId, content: WireId) {
        self.ops.push(MemOp::Store { addr, content });
        self.values.insert([0, 0, 0, 0], [0, 0, 0, 0]);
    }

    pub fn load(&mut self, back: &mut Backend, addr: WireId) -> WireId {
        let content = back.new_wire();
        self.ops.push(MemOp::Load { addr, content });
        // TODO: copy values[addr] into the new wire.
        return content;
    }
}

impl Drop for Memory {
    fn drop(&mut self) {
        if !self.finished {
            panic!("Memory.finish() must be called.");
        }
    }
}

#[test]
fn test_zkif_backend() {
    let mut back = Backend::new();
    let mut mem = Memory::new();
    let mut regs = vec![WireId(0); 4];
    for reg in regs.iter_mut() {
        *reg = back.new_wire();
    }

    println!("Initial registers: {:?}", regs);
    back.print_cost();
    println!();

    {
        let instr = FixedInstr {
            oplabel: 0,
            reglabel0: 0,
            reglabel1: 1,
            reglabel2: 2,
        };
        back.push_instr(&mut regs, &instr);
        println!();
    }

    let possible_ops = (0..8).collect::<Vec<OpLabel>>();
    {
        let sec_instr = SecretInstr {
            possible_opcodes: &possible_ops,
            opcode: back.new_wire(),
            reglabel0: back.new_wire(),
            reglabel1: back.new_wire(),
            reglabel2: back.new_wire(),
        };
        back.push_secret_instr(&mut regs, &sec_instr);
        println!();
    }
    {
        let sec_instr = SecretInstr {
            possible_opcodes: &possible_ops,
            opcode: back.new_wire(),
            reglabel0: back.new_wire(),
            reglabel1: back.new_wire(),
            reglabel2: back.new_wire(),
        };
        back.push_secret_instr(&mut regs, &sec_instr);
        println!();
    }

    mem.finish(&mut back);
}


impl fmt::Debug for WireId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        debug::write_wire_name(self.0, f)
    }
}
