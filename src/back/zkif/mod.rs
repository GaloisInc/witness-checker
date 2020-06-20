mod debug;

use std::fmt;
use colored::Colorize;
use std::collections::HashMap;

// TODO: Use actual types.
type OpCode = usize;
type RegLabel = usize;

type WireId = u64;
type WireValue = [u64; 4];

#[derive(Copy, Clone)]
pub struct WirePack(WireId);


pub struct Backend {
    free_var_id: u64,

    cost: usize,
    last_printed_cost: usize,
}

impl Backend {
    pub fn new() -> Backend { Backend { free_var_id: 1, cost: 0, last_printed_cost: 0 } }

    pub fn allocate(&mut self) -> WirePack {
        let new_id = self.free_var_id;
        self.free_var_id += 1;
        self.cost += 1 + 16; // Word size, boolean-ness.
        return WirePack(new_id);
    }

    pub fn print_cost(&mut self) {
        println!("{}", format!("Cost of the above: {}", self.cost - self.last_printed_cost).italic());
        self.last_printed_cost = self.cost;
    }
}

// Core execution units.
impl Backend {
    // new wire = operation(v0 v1 v2)
    pub fn push_operation(&mut self, opcode: OpCode, regval0: WirePack, regval1: WirePack, regval2: WirePack) -> WirePack {
        // TODO: use the implementation for the given opcode.
        let regout = self.allocate();
        self.cost += 30;
        println!("{:?}\t= operation_{}( {:?}, {:?}, {:?})", regout, opcode, regval0, regval1, regval2);
        return regout;
    }

    // new wire = inputs[index]
    pub fn push_demux(&mut self, inputs: &[WirePack], index: WirePack) -> WirePack {
        // TODO: use secret index.
        let regout = self.allocate();
        self.cost += 1 + inputs.len();
        println!("{:?}\t= demux selects {:?} from {:?}", regout, index, inputs);
        return regout;
    }

    // regs[index] = new wire equal to new_value.
    // regs[i] = new wire equal to regs[i], for i != index.
    pub fn push_update(&mut self, regs: &mut [WirePack], index: WirePack, new_value: WirePack) {
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
    opcode: WirePack,
    reglabel0: WirePack,
    reglabel1: WirePack,
    reglabel2: WirePack,
}

// CPU components. Compose and connect core components.
impl Backend {
    pub fn push_instr(&mut self, regs: &mut [WirePack], instr: &FixedInstr) {
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

    pub fn push_secret_instr(&mut self, regvals: &mut [WirePack], instr: &SecretInstr) {
        println!("secret instruction {:?}( {:?}, {:?}, {:?} )", instr.opcode, instr.reglabel0, instr.reglabel1, instr.reglabel2);
        println!("// Pick the register inputs from all possible registers.");
        let regval0 = self.push_demux(regvals, instr.reglabel0);
        let regval1 = self.push_demux(regvals, instr.reglabel1);
        let regval2 = self.push_demux(regvals, instr.reglabel2);
        self.print_cost();

        println!("// Execute all possible operations.");
        let possible_results = instr.possible_opcodes.iter().map(|op|
            self.push_operation(*op, regval0, regval1, regval2)
        ).collect::<Vec<WirePack>>();
        self.print_cost();

        println!("// Pick the result of the actual operation.");
        let result = self.push_demux(&possible_results, instr.opcode);

        self.push_update(regvals, instr.reglabel0, result);
        self.print_cost();
    }
}

pub struct Memory {
    ops: Vec<MemOp>,
    values: HashMap<WireValue, WireValue>,
    finished: bool,
}

enum MemOp {
    Store { addr: WirePack, content: WirePack },
    Load { addr: WirePack, content: WirePack },
}

impl Memory {
    pub fn new() -> Memory {
        Memory { ops: vec![], values: HashMap::new(), finished: false }
    }
    pub fn finish(mut self, back: &mut Backend) {
        // TODO: store/load consistency check.
        self.finished = true;
    }

    pub fn store(&mut self, addr: WirePack, content: WirePack) {
        self.ops.push(MemOp::Store { addr, content });
        self.values.insert([0, 0, 0, 0], [0, 0, 0, 0]);
    }

    pub fn load(&mut self, back: &mut Backend, addr: WirePack) -> WirePack {
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
    let mut regs = vec![WirePack(0); 4];
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


impl fmt::Debug for WirePack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        debug::write_var_name(self.0, f)
    }
}
