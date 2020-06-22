use super::backend::{Backend, WireId, OpLabel};
use super::mem::PackedValue;

type RegLabel = usize;

// A publicly-known instruction (fixed operation and register labels).
pub struct FixedInstr {
    pub oplabel: OpLabel,
    pub reglabel0: RegLabel,
    pub reglabel1: RegLabel,
    pub reglabel2: RegLabel,
}

impl FixedInstr {
    // Encode the instruction so it can be stored in memory,
    // and decoded by SecretInstr.decode_instr().
    pub fn encode_instr(&self) -> PackedValue {
        [0, 0, 0, 0]
    }
}

// An instruction with secret operation and register labels.
pub struct SecretInstr {
    opcode: WireId,
    reglabel0: WireId,
    reglabel1: WireId,
    reglabel2: WireId,
}

impl SecretInstr {
    // Decode a secret instruction from a wire
    // holding a value from FixedInstr.encode_instr().
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

// A description of what a secret execution step may do.
// The more capabilities, the more expensive.
pub struct StepCapabilities {
    pub possible_alu_ops: Vec<OpLabel>,
    pub possible_flow_ops: Vec<OpLabel>,
}

impl StepCapabilities {
    pub fn new() -> StepCapabilities {
        StepCapabilities {
            possible_alu_ops: (0..12).collect::<Vec<OpLabel>>(),
            possible_flow_ops: (0..4).collect::<Vec<OpLabel>>(),
        }
    }
}

// CPU components. Compose and connect core components.

#[derive(Clone, Debug)]
pub struct MachineState {
    pub registers: Vec<WireId>,
    pub flag: WireId,
    pub pc: WireId,
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

        let (new_reg0, new_flag, new_pc) = if is_flow(instr.oplabel) {
            // Flow instructions update pc and copy the rest.
            let jump_pc = back.push_flow_op(
                instr.oplabel,
                self.flag,
                self.pc,
                self.registers[instr.reglabel2]);
            (self.registers[instr.reglabel0], self.flag, jump_pc)
        } else {
            // ALU instructions update a register, the flag, and increment pc.
            let (new_reg0, new_flag) = back.push_alu_op(
                instr.oplabel,
                self.registers[instr.reglabel0],
                self.registers[instr.reglabel1],
                self.registers[instr.reglabel2]);
            let next_pc = back.new_wire(); // TODO: pc+1
            (new_reg0, new_flag, next_pc)
        };

        self.registers[instr.reglabel0] = new_reg0;
        self.flag = new_flag;
        self.pc = new_pc;

        println!("registers[{}]\t= {:?}", instr.reglabel0, new_reg0);
        println!("pc = {:?}, flag = {:?}", new_pc, new_flag);
        back.cost_est.print_cost();
    }

    pub fn push_secret_instr(&mut self, back: &mut Backend, capab: &StepCapabilities, instr: &SecretInstr) {
        println!("secret instruction {:?}( {:?}, {:?}, {:?} )", instr.opcode, instr.reglabel0, instr.reglabel1, instr.reglabel2);

        println!("// Pick the register inputs from all possible registers.");
        let arg0 = back.push_muxer(&self.registers, instr.reglabel0);
        let arg1 = back.push_muxer(&self.registers, instr.reglabel1);
        let arg2 = back.push_muxer(&self.registers, instr.reglabel2);
        back.cost_est.print_cost();

        println!("// Execute all possible ALU operations.");
        let possible_alu_results = capab.possible_alu_ops.iter().map(|op|
            back.push_alu_op(*op, arg0, arg1, arg2)
        ).collect::<Vec<(WireId, WireId)>>();
        back.cost_est.print_cost();

        println!("// Pick the result of the actual ALU operation.");
        let (alu_result, alu_flag) = back.push_muxer_pair(&possible_alu_results, instr.opcode);
        let alu_pc = back.new_wire(); // Increment PC. TODO: pc+1

        println!("// Execute all possible FLOW operations.");
        let possible_flow_pcs = capab.possible_flow_ops.iter().map(|op|
            back.push_flow_op(*op, self.flag, self.pc, arg2)
        ).collect::<Vec<WireId>>();
        back.cost_est.print_cost();

        println!("// Pick the PC after the actual FLOW operation.");
        let flow_pc = back.push_muxer(&possible_flow_pcs, instr.opcode);
        let flow_result = arg0; // Copy.
        let flow_flag = self.flag; // Copy.
        // TODO: deal with the offset of flow opcodes rather than index in the muxer above.

        println!("// Pick the state after either the ALU or FLOW operation.");
        let is_flow = self.push_opcode_is_flow(back, instr.opcode);
        let result = back.push_muxer(&[alu_result, flow_result], is_flow);
        let new_flag = back.push_muxer(&[alu_flag, flow_flag], is_flow);
        let new_pc = back.push_muxer(&[alu_pc, flow_pc], is_flow);

        // TODO: assert that the opcode is one of the possible opcodes.

        println!("// Write the new state.");
        back.push_demuxer(&mut self.registers, instr.reglabel0, result);
        self.flag = new_flag;
        self.pc = new_pc;

        println!("pc = {:?}, flag = {:?}", new_pc, new_flag);
        back.cost_est.print_cost();
    }

    pub fn push_opcode_is_flow(&self, back: &mut Backend, opcode: WireId) -> WireId {
        // TODO: decode.
        let is_flow = back.new_wire();
        return is_flow;
    }
}

pub fn is_flow(op: OpLabel) -> bool {
    return op > 2;
}