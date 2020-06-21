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

    pub fn true_wire(&self) -> WireId { WireId(0) }

    pub fn print_cost(&mut self) {
        //println!("{}", format!("Cost of the above: {}", self.cost - self.last_printed_cost).yellow().italic());
        self.last_printed_cost = self.cost;
    }
}

// Core execution units.
impl Backend {
    // result, flag = operation(arg0 arg1 arg2)
    pub fn push_operation(&mut self, opcode: OpLabel, regval0: WireId, regval1: WireId, regval2: WireId, flag: WireId, pc: WireId) -> (WireId, WireId, WireId) {
        if is_flow(opcode) {
            let jump_pc = self.push_flow_op(opcode, flag, pc, regval2);
            return (regval0, flag, jump_pc);
        } else {
            let (new_regval0, new_flag) = self.push_alu_op(opcode, regval0, regval1, regval2);
            let next_pc = self.new_wire(); // TODO: pc+1
            return (new_regval0, new_flag, next_pc);
        }
    }

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

    pub fn push_decode_op_type(&mut self, opcode: WireId) -> (WireId) {
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

pub fn is_flow(op: OpLabel) -> bool {
    return op > 2;
}

const num_ops: usize = 4;


pub struct FixedInstr {
    oplabel: OpLabel,
    reglabel0: RegLabel,
    reglabel1: RegLabel,
    reglabel2: RegLabel,
}

impl FixedInstr {
    pub fn encode_instr(&self) -> PackedValue {
        [0, 0, 0, 0]
    }
}

pub struct SecretInstr {
    opcode: WireId,
    reglabel0: WireId,
    reglabel1: WireId,
    reglabel2: WireId,
}

impl SecretInstr {
    pub fn decode_instr(back: &mut Backend, packed: WireId) -> SecretInstr {
        // TODO: actual decoding.
        SecretInstr {
            opcode: back.new_wire(),
            reglabel0: back.new_wire(),
            reglabel1: back.new_wire(),
            reglabel2: back.new_wire(),
        }
    }
}

pub struct TransitionCapabilities {
    possible_alu_ops: Vec<OpLabel>,
    possible_flow_ops: Vec<OpLabel>,
}

// CPU components. Compose and connect core components.

#[derive(Clone, Debug)]
pub struct MachineState {
    registers: Vec<WireId>,
    flag: WireId,
    pc: WireId,
}

impl MachineState {
    pub fn new(back: &mut Backend) -> MachineState {
        MachineState {
            registers: (0..4).map(|_| back.new_wire()).collect(),
            flag: back.new_wire(),
            pc: back.new_wire(),
        }
    }

    pub fn push_fixed_instr(&mut self, back: &mut Backend, instr: &FixedInstr) {
        println!("fixed instruction op_{}( reg_{}, reg_{}, reg_{} )", instr.oplabel, instr.reglabel0, instr.reglabel1, instr.reglabel2);

        let (new_reg0, new_flag, new_pc) = back.push_operation(
            instr.oplabel,
            self.registers[instr.reglabel0],
            self.registers[instr.reglabel1],
            self.registers[instr.reglabel2],
            self.flag,
            self.pc,
        );

        self.registers[instr.reglabel0] = new_reg0;
        self.flag = new_flag;
        self.pc = new_pc;

        println!("registers[{}]\t= {:?}", instr.reglabel0, new_reg0);
        println!("pc = {:?}, flag = {:?}", new_pc, new_flag);
        back.print_cost();
    }

    pub fn push_secret_instr(&mut self, back: &mut Backend, capab: &TransitionCapabilities, instr: &SecretInstr) {
        println!("secret instruction {:?}( {:?}, {:?}, {:?} )", instr.opcode, instr.reglabel0, instr.reglabel1, instr.reglabel2);

        println!("// Pick the register inputs from all possible registers.");
        let arg0 = back.push_demux(&self.registers, instr.reglabel0);
        let arg1 = back.push_demux(&self.registers, instr.reglabel1);
        let arg2 = back.push_demux(&self.registers, instr.reglabel2);
        back.print_cost();

        println!("// Execute all possible ALU operations.");
        let possible_alu_results = capab.possible_alu_ops.iter().map(|op|
            back.push_alu_op(*op, arg0, arg1, arg2)
        ).collect::<Vec<(WireId, WireId)>>();
        back.print_cost();

        println!("// Pick the result of the actual ALU operation.");
        let (alu_result, alu_flag) = back.push_demux_tuple(&possible_alu_results, instr.opcode);
        let alu_pc = back.new_wire(); // Increment PC. TODO: pc+1

        println!("// Execute all possible FLOW operations.");
        let possible_flow_pcs = capab.possible_flow_ops.iter().map(|op|
            back.push_flow_op(*op, self.flag, self.pc, arg2)
        ).collect::<Vec<WireId>>();
        back.print_cost();

        println!("// Pick the PC after the actual FLOW operation.");
        let flow_pc = back.push_demux(&possible_flow_pcs, instr.opcode);
        let flow_result = arg0; // Copy.
        let flow_flag = self.flag; // Copy.
        // TODO: deal with the offset of flow opcodes rather than index in the demux above.

        println!("// Pick the state after either the ALU or FLOW operation.");
        let is_flow = back.push_decode_op_type(instr.opcode);
        let result = back.push_demux(&[alu_result, flow_result], is_flow);
        let new_flag = back.push_demux(&[alu_flag, flow_flag], is_flow);
        let new_pc = back.push_demux(&[alu_pc, flow_pc], is_flow);

        println!("// Write the new state.");
        back.push_update(&mut self.registers, instr.reglabel0, result);
        self.flag = new_flag;
        self.pc = new_pc;

        println!("pc = {:?}, flag = {:?}", new_pc, new_flag);
        back.print_cost();
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
    Store { condition: WireId, address: WireId, content: WireId },
    Load { condition: WireId, address: WireId, content: WireId },
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

    pub fn store(&mut self, condition: WireId, address: WireId, content: WireId) {
        self.ops.push(MemOp::Store { condition, address, content });
        // TODO: conditionally store the content.
        if false {
            self.values.insert([0, 0, 0, 0], [0, 0, 0, 0]);
        }
    }

    pub fn load(&mut self, back: &mut Backend, condition: WireId, address: WireId) -> WireId {
        let content = back.new_wire();
        self.ops.push(MemOp::Load { condition, address, content });
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
    let mut state = MachineState::new(&mut back);
    let mut mem = Memory::new();
    let true_wire = back.true_wire();

    println!("Initial state: {:#?}", state);
    back.print_cost();
    println!();

    {
        let instr = FixedInstr {
            oplabel: 0,
            reglabel0: 0,
            reglabel1: 1,
            reglabel2: 2,
        };
        state.push_fixed_instr(&mut back, &instr);
        println!();
    }

    let spec = TransitionCapabilities {
        possible_alu_ops: (0..num_ops - 2).collect::<Vec<OpLabel>>(),
        possible_flow_ops: (0..2).collect::<Vec<OpLabel>>(),
    };

    for _ in 0..2 {
        let instr_in_pc = mem.load(&mut back, true_wire, state.pc);
        let instr = SecretInstr::decode_instr(&mut back, instr_in_pc);

        state.push_secret_instr(&mut back, &spec, &instr);

        println!();
    }

    mem.finish(&mut back);
}


impl fmt::Debug for WireId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        debug::write_wire_name(self.0, f)
        //write!(f, "&{:3}", self.0.to_string().blue())
    }
}
