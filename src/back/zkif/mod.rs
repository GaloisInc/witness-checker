mod debug;

use std::fmt;

// TODO: Use actual types.
type OpCode = usize;
type RegLabel = usize;

#[derive(Copy, Clone)]
pub struct WirePack(u64);


pub struct Backend {
    free_var_id: u64,
}

impl Backend {
    pub fn new() -> Backend { Backend { free_var_id: 1 } }

    pub fn allocate(&mut self) -> WirePack {
        let new_id = self.free_var_id;
        self.free_var_id += 1;
        return WirePack(new_id);
    }
}

// Low-level execution units.
impl Backend {
    // new wire = operation(v0 v1 v2)
    pub fn push_alu(&mut self, opcode: OpCode, regval0: WirePack, regval1: WirePack, regval2: WirePack) -> WirePack {
// TODO: use the implementation for the given opcode.
        let regout = self.allocate();
        println!("{:?}\t= operation_{}( {:?}, {:?}, {:?})", regout, opcode, regval0, regval1, regval2);
        return regout;
    }

    // new wire = inputs[index]
    pub fn push_demux(&mut self, inputs: &[WirePack], index: WirePack) -> WirePack {
// TODO: use secret index.
        let regout = self.allocate();
        println!("{:?}\t= demux picks {:?} from {:?}", regout, index, inputs);
        return regout;
    }

    // regs[index] = new wire equal to new_value.
// regs[i] = new wire equal to regs[i], for i != index.
    pub fn push_update(&mut self, regs: &mut [WirePack], index: WirePack, new_value: WirePack) {
        for i in 0..regs.len() {
// TODO: condition on secret index.
            regs[i] = self.allocate();
        }
        println!("regs[{:?}] = {:?}", index, new_value);
    }

    /*pub fn push_decoder(&self, input: WirePack, index: WirePack, num_outputs: usize) -> Vec<WirePack> {
        let mut outputs = vec![0; num_outputs];
        outputs[0] = input;
        return outputs;
    }*/
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

// High-level CPU components. Compose and connect low-level components.
impl Backend {
    pub fn push_instr(&mut self, regs: &mut [WirePack], instr: &FixedInstr) {
        let result = self.push_alu(
            instr.opcode,
            regs[instr.reglabel0],
            regs[instr.reglabel1],
            regs[instr.reglabel2]);
        regs[instr.reglabel0] = result;
        println!("push_instr registers[{}] = {:?}", instr.reglabel0, result);
    }

    pub fn push_secret_instr(&mut self, regvals: &mut [WirePack], instr: &SecretInstr) {
// Pick the register inputs from all possible registers.
        let regval0 = self.push_demux(regvals, instr.reglabel0);
        let regval1 = self.push_demux(regvals, instr.reglabel1);
        let regval2 = self.push_demux(regvals, instr.reglabel2);

// Execute all possible operations.
        let possible_results = instr.possible_opcodes.iter().map(|op|
            self.push_alu(*op, regval0, regval1, regval2)
        ).collect::<Vec<WirePack>>();

// Pick the result of the actual operation.
        let result = self.push_demux(&possible_results, instr.opcode);

        self.push_update(regvals, instr.reglabel0, result);
        println!("push_secret_instr new registers: {:?}", regvals);
    }
}

#[test]
fn test_zkif_backend() {
    let mut back = Backend::new();
    let mut regs = vec![WirePack(0); 4];
    for reg in regs.iter_mut() {
        *reg = back.allocate();
    }
    println!("Initial registers: {:?}", regs);
    println!();

    let instr = FixedInstr {
        opcode: 0,
        reglabel0: 0,
        reglabel1: 1,
        reglabel2: 2,
    };
    back.push_instr(&mut regs, &instr);
    println!();

    let possible_ops = vec![0, 1];
    let sec_instr = SecretInstr {
        possible_opcodes: &possible_ops,
        opcode: WirePack(0),
        reglabel0: WirePack(0),
        reglabel1: WirePack(1),
        reglabel2: WirePack(2),
    };
    back.push_secret_instr(&mut regs, &sec_instr);
}


impl fmt::Debug for WirePack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        debug::write_var_name(self.0, f)
    }
}
