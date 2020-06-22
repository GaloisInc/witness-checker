use super::backend::{Backend, WireId, OpLabel, PackedValue};
use crate::back::zkif::mem::Memory;
use super::debug::comment;

type RegLabel = usize;

#[derive(Debug)]
pub enum RegOrValue {
    Reg(RegLabel),
    Val(PackedValue),
}

// A publicly-known instruction (fixed operation and register labels).
pub struct StaticInstr {
    pub oplabel: OpLabel,
    pub reglabel0: RegLabel,
    pub reglabel1: RegLabel,
    pub reglabel2: RegOrValue,
}

impl StaticInstr {
    // Encode the instruction so it can be stored in memory,
    // and decoded by SecretInstr.decode_instr().
    pub fn encode_instr(&self) -> PackedValue {
        [0, 0, 0, 0]
    }
}

// An instruction with secret operation and register labels.
pub struct DynInstr {
    opcode: WireId,
    reglabel0: WireId,
    reglabel1: WireId,
    reglabel2: WireId,
    reg2_immediate: WireId,
}

impl DynInstr {
    // Decode a secret instruction from a wire
    // holding a value from FixedInstr.encode_instr().
    pub fn decode_instr(back: &mut Backend, capab: &StepCapabilities, packed: WireId) -> DynInstr {
        // TODO: actual decoding and validation.
        DynInstr {
            opcode: back.new_wire(),
            reglabel0: back.new_wire(),
            reglabel1: back.new_wire(),
            reglabel2: back.new_wire(),
            reg2_immediate: back.new_wire(),
        }
    }
}

// A description of what a dynamic execution step may do.
// The more capabilities, the more expensive.
pub struct StepCapabilities {
    pub possible_alu_ops: Vec<OpLabel>,
    pub possible_flow_ops: Vec<OpLabel>,
    pub possible_mem_store: bool,
    pub possible_mem_load: bool,
}

impl StepCapabilities {
    pub fn new() -> StepCapabilities {
        StepCapabilities {
            possible_alu_ops: (0..12).collect::<Vec<OpLabel>>(),
            possible_flow_ops: (0..4).collect::<Vec<OpLabel>>(),
            possible_mem_store: true,
            possible_mem_load: true,
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

    pub fn push_static_instr(&mut self, back: &mut Backend, instr: &StaticInstr) {
        println!("static instruction op_{}( reg_{}, reg_{}, {:?} )", instr.oplabel, instr.reglabel0, instr.reglabel1, instr.reglabel2);

        let arg2 = match instr.reglabel2 {
            RegOrValue::Reg(label) => self.registers[label],
            RegOrValue::Val(value) => back.wire_constant(value),
        };

        let (new_reg0, new_flag, new_pc) = if Self::is_flow(instr.oplabel) {
            // Flow instructions update pc and copy the rest.
            let jump_pc = back.push_flow_op(
                instr.oplabel,
                self.flag,
                self.pc,
                arg2);
            (self.registers[instr.reglabel0], self.flag, jump_pc)
        } else {
            // ALU instructions update a register, the flag, and increment pc.
            let (new_reg0, new_flag) = back.push_alu_op(
                instr.oplabel,
                self.registers[instr.reglabel0],
                self.registers[instr.reglabel1],
                arg2);
            let next_pc = back.new_wire(); // TODO: pc+1
            (new_reg0, new_flag, next_pc)
        };
        // TODO: mem store and load.

        self.registers[instr.reglabel0] = new_reg0;
        self.flag = new_flag;
        self.pc = new_pc;

        println!("registers[{}]\t= {:?}", instr.reglabel0, new_reg0);
        println!("pc = {:?}, flag = {:?}", new_pc, new_flag);
        back.cost_est.print_cost();
    }

    pub fn push_dynamic_instr(&mut self, back: &mut Backend, mem: &mut Memory, capab: &StepCapabilities, instr: &DynInstr) {
        println!("dynamic instruction {:?}( {:?}, {:?}, {:?} )", instr.opcode, instr.reglabel0, instr.reglabel1, instr.reglabel2);

        comment("// Pick the register inputs from all possible registers.");
        let arg0 = back.push_muxer(&self.registers, instr.reglabel0);
        let arg1 = back.push_muxer(&self.registers, instr.reglabel1);
        let arg2_reg = back.push_muxer(&self.registers, instr.reglabel2);
        let arg2 = back.push_muxer(&[arg2_reg, instr.reglabel2], instr.reg2_immediate);
        back.cost_est.print_cost();

        comment("// Execute all possible ALU operations.");
        let possible_alu_results = capab.possible_alu_ops.iter().map(|op|
            back.push_alu_op(*op, arg0, arg1, arg2)
        ).collect::<Vec<(WireId, WireId)>>();

        comment("// Pick the result of the actual ALU operation.");
        let (alu_result, alu_flag) = back.push_muxer_pair(&possible_alu_results, instr.opcode);
        back.cost_est.print_cost();

        comment("// Execute all possible FLOW operations.");
        let next_pc = back.new_wire(); // Increment PC. TODO: pc+1
        let possible_flow_pcs = capab.possible_flow_ops.iter().map(|op|
            back.push_flow_op(*op, self.flag, self.pc, arg2)
        ).collect::<Vec<WireId>>();

        comment("// Pick the PC after the actual FLOW operation.");
        let flow_pc = back.push_muxer(&possible_flow_pcs, instr.opcode);
        // TODO: deal with the offset of flow opcodes rather than index in the muxer above.
        back.cost_est.print_cost();

        comment("// Execute possible MEM load and store operations.");
        if capab.possible_mem_store {
            let is_store = Self::push_is_mem_store(back, instr.opcode);
            mem.store(back, is_store, arg2, arg0);
        }
        if capab.possible_mem_load {
            let is_load = Self::push_is_mem_load(back, instr.opcode);
            mem.load(back, is_load, arg2);
        }
        back.cost_est.print_cost();

        comment("// Pick the state after either the ALU or FLOW or MEM operation.");
        let op_type = Self::push_opcode_type(back, instr.opcode);
        let copy_arg0 = arg0;
        let copy_flag = self.flag;

        let result = back.push_muxer(&[alu_result, copy_arg0, copy_arg0], op_type);
        let new_flag = back.push_muxer(&[alu_flag, copy_flag, copy_flag], op_type);
        let new_pc = back.push_muxer(&[next_pc, flow_pc, next_pc], op_type);

        comment("// Write the new state.");
        back.push_demuxer(&mut self.registers, instr.reglabel0, result);
        self.flag = new_flag;
        self.pc = new_pc;

        println!("pc = {:?}, flag = {:?}", new_pc, new_flag);
        back.cost_est.print_cost();
    }

    pub fn push_dynamic_instr_at_pc(&mut self, back: &mut Backend, mem: &mut Memory, capab: &StepCapabilities) {
        let wire_true = back.wire_one();
        let instr_at_pc = mem.load(back, wire_true, self.pc);
        let instr = DynInstr::decode_instr(back, capab, instr_at_pc);
        self.push_dynamic_instr(back, mem, capab, &instr);
    }

    // Helpers.

    pub fn push_opcode_type(back: &mut Backend, opcode: WireId) -> WireId {
        let _ = back.represent_as_one_hot(opcode);
        // TODO: decode "is alu", "is flow", "is mem".
        back.cost_est.cost += 2;
        back.new_wire()
    }

    pub fn push_is_mem_store(back: &mut Backend, opcode: WireId) -> WireId {
        let _ = back.represent_as_one_hot(opcode);
        // TODO: decode "is store"
        back.cost_est.cost += 1;
        back.new_wire()
    }

    pub fn push_is_mem_load(back: &mut Backend, opcode: WireId) -> WireId {
        let _ = back.represent_as_one_hot(opcode);
        // TODO: decode "is load"
        back.cost_est.cost += 1;
        back.new_wire()
    }

    pub fn is_flow(op: OpLabel) -> bool {
        return op > 2; // TODO.
    }
}
