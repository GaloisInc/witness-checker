mod debug;

use std::fmt;
use colored::Colorize;
use std::collections::HashMap;

// TODO: Use actual types.
type OpCode = usize;
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

    pub fn allocate(&mut self) -> WireId {
        self.wire_reprs.push(WireRepr { packed_zid: None, bit_zids: vec![] });
        return WireId(self.wire_reprs.len() - 1);
    }

    pub fn print_cost(&mut self) {
        println!("{}", format!("Cost of the above: {}", self.cost - self.last_printed_cost).italic());
        self.last_printed_cost = self.cost;
    }
}

// Core execution units.
impl Backend {
    // new wire = operation(v0 v1 v2)
    pub fn push_operation(&mut self, opcode: OpCode, regval0: WireId, regval1: WireId, regval2: WireId) -> WireId {
        // TODO: use the implementation for the given opcode.
        let regout = self.allocate();
        self.cost += 30;
        println!("{:?}\t= operation_{}( {:?}, {:?}, {:?})", regout, opcode, regval0, regval1, regval2);
        return regout;
    }

    // new wire = inputs[index]
    pub fn push_demux(&mut self, inputs: &[WireId], index: WireId) -> WireId {
        // TODO: use secret index.
        let regout = self.allocate();
        self.cost += 1 + inputs.len();
        println!("{:?}\t= demux selects {:?} from {:?}", regout, index, inputs);
        return regout;
    }

    // regs[index] = new wire equal to new_value.
    // regs[i] = new wire equal to regs[i], for i != index.
    pub fn push_update(&mut self, regs: &mut [WireId], index: WireId, new_value: WireId) {
        for i in 0..regs.len() {
            // TODO: condition on secret index.
            regs[i] = self.allocate();
        }
        self.cost += 1 + regs.len();
        println!("regs[{:?}]\t= {:?} in new registers {:?}", index, new_value, regs);
    }
}

pub struct FixedInstr {
    opcode: OpCode,
    reglabel0: RegLabel,
    reglabel1: RegLabel,
    reglabel2: RegLabel,
}

pub struct SecretInstr<'a> {
    possible_opcodes: &'a [OpCode],
    opcode: WireId,
    reglabel0: WireId,
    reglabel1: WireId,
    reglabel2: WireId,
}

// CPU components. Compose and connect core components.
impl Backend {
    pub fn push_instr(&mut self, regs: &mut [WireId], instr: &FixedInstr) {
        println!("instruction operation_{}( {}, {}, {} )", instr.opcode, instr.reglabel0, instr.reglabel1, instr.reglabel2);
        let result = self.push_operation(
            instr.opcode,
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
            self.push_operation(*op, regval0, regval1, regval2)
        ).collect::<Vec<WireId>>();
        self.print_cost();

        println!("// Pick the result of the actual operation.");
        let result = self.push_demux(&possible_results, instr.opcode);

        self.push_update(regvals, instr.reglabel0, result);
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
        let content = back.allocate();
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
        *reg = back.allocate();
    }

    println!("Initial registers: {:?}", regs);
    back.print_cost();
    println!();

    {
        let instr = FixedInstr {
            opcode: 0,
            reglabel0: 0,
            reglabel1: 1,
            reglabel2: 2,
        };
        back.push_instr(&mut regs, &instr);
        println!();
    }

    let possible_ops = (0..8).collect::<Vec<OpCode>>();
    {
        let sec_instr = SecretInstr {
            possible_opcodes: &possible_ops,
            opcode: back.allocate(),
            reglabel0: back.allocate(),
            reglabel1: back.allocate(),
            reglabel2: back.allocate(),
        };
        back.push_secret_instr(&mut regs, &sec_instr);
        println!();
    }
    {
        let sec_instr = SecretInstr {
            possible_opcodes: &possible_ops,
            opcode: back.allocate(),
            reglabel0: back.allocate(),
            reglabel1: back.allocate(),
            reglabel2: back.allocate(),
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
