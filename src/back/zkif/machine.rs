use super::prototype_backend::{PrototypeBackend, WireId, PackedValue};
use super::gadgetlib::{push_alu_op, push_flow_op, push_muxer, push_muxer_pair, push_demuxer};
use crate::back::zkif::mem::Memory;
use super::debug::comment;

// TODO: Use types and opcodes from the rest of the package.
pub type OpLabel = usize;
pub type RegLabel = usize;

#[derive(Debug)]
pub enum RegOrValue {
    Reg(RegLabel),
    Val(PackedValue),
}

// A publicly-known instruction (fixed operation and register labels).
pub struct StaticInstr {
    pub op_label: OpLabel,
    pub reg_label0: RegLabel,
    pub reg_label1: RegLabel,
    pub reg_label2: RegOrValue,
}

impl StaticInstr {
    // Encode the instruction so it can be stored in memory,
    // and decoded by SecretInstr.decode_instr().
    pub fn encode_instr(&self) -> PackedValue {
        [0, 0, 0, 0]
    }
}

// An instruction with secret operation and register labels.
#[derive(Debug)]
pub struct DynInstr {
    op_label: WireId,
    reg_label0: WireId,
    reg_label1: WireId,
    reg_label2: WireId,
    label2_immediate: WireId,
}

impl DynInstr {
    // Decode a secret instruction from a wire
    // holding a value from FixedInstr.encode_instr().
    pub fn decode_instr(back: &mut PrototypeBackend, capab: &StepCapabilities, packed: WireId) -> DynInstr {
        // TODO: actual decoding and validation.
        let instr = DynInstr {
            op_label: back.new_wire(),
            reg_label0: back.new_wire(),
            reg_label1: back.new_wire(),
            reg_label2: back.new_wire(),
            label2_immediate: back.new_wire(),
        };

        println!("{:?}\t= decode_instr( {:?} )", instr, packed);
        instr
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
    pub fn new(back: &mut PrototypeBackend) -> MachineState {
        MachineState {
            registers: (0..4).map(|_| back.new_wire()).collect(),
            flag: back.new_wire(),
            pc: back.new_wire(),
        }
    }

    pub fn push_static_instr(&mut self, back: &mut PrototypeBackend, mem: &mut Memory, instr: &StaticInstr) {
        println!("static instruction op_{}( reg_{}, reg_{}, {:?} )", instr.op_label, instr.reg_label0, instr.reg_label1, instr.reg_label2);

        let arg2 = match instr.reg_label2 {
            RegOrValue::Reg(label) => self.registers[label],
            RegOrValue::Val(value) => back.wire_constant(value),
        };
        let next_pc = back.new_wire(); // TODO: pc+1

        match Self::get_op_type(instr.op_label) {
            0 => {
                // ALU instructions update a register, the flag, and increment pc.
                let (new_reg0, new_flag) = push_alu_op(
                    back,
                    instr.op_label,
                    self.registers[instr.reg_label0],
                    self.registers[instr.reg_label1],
                    arg2);
                self.registers[instr.reg_label0] = new_reg0;
                self.flag = new_flag;
                self.pc = next_pc;
            }
            1 => {
                // Flow instructions update pc and copy the rest.
                let jump_pc = push_flow_op(
                    back,
                    instr.op_label,
                    self.flag,
                    next_pc,
                    arg2);
                self.pc = jump_pc;
            }
            _ => {
                // Memory instructions.
                // TODO: actual opcodes.
                if instr.op_label == 6 {
                    let true_wire = back.wire_one();
                    mem.store(back, true_wire, arg2, self.registers[instr.reg_label0]);
                }
                if instr.op_label == 7 {
                    let new_reg0 = mem.load(back, arg2);
                    self.registers[instr.reg_label0] = new_reg0;
                }
                self.pc = next_pc;
            }
        };

        println!("registers[{}]\t= {:?}", instr.reg_label0, self.registers[instr.reg_label0]);
        println!("pc = {:?}, flag = {:?}", self.pc, self.flag);
        back.cost_est.print_cost();
    }


    pub fn push_dynamic_instr(&mut self, back: &mut PrototypeBackend, mem: &mut Memory, capab: &StepCapabilities, instr: &DynInstr) {
        //println!("dynamic instruction {:?}( {:?}, {:?}, {:?} )", instr.opcode, instr.reglabel0, instr.reglabel1, instr.reglabel2);

        comment("// Pick the register inputs from all possible registers.");
        let arg0 = push_muxer(back, &self.registers, instr.reg_label0);
        let arg1 = push_muxer(back, &self.registers, instr.reg_label1);
        let arg2_from_reg = push_muxer(back, &self.registers, instr.reg_label2);
        let arg2 = push_muxer(back, &[arg2_from_reg, instr.reg_label2], instr.label2_immediate);

        // Default results when not updated.
        let copy_arg0 = arg0;
        let copy_flag = self.flag;
        let next_pc = Self::push_increment_pc(back, self.pc);
        back.cost_est.print_cost();

        comment("// Execute all possible ALU operations.");
        let possible_alu_results = capab.possible_alu_ops.iter().map(|op|
            push_alu_op(back, *op, arg0, arg1, arg2)
        ).collect::<Vec<(WireId, WireId)>>();

        comment("// Pick the (result, flag) of the actual ALU operation.");
        let (alu_result, alu_flag) = push_muxer_pair(back, &possible_alu_results, instr.op_label);
        back.cost_est.print_cost();

        comment("// Execute all possible FLOW operations.");
        let possible_flow_pcs = capab.possible_flow_ops.iter().map(|op|
            push_flow_op(back, *op, self.flag, next_pc, arg2)
        ).collect::<Vec<WireId>>();

        comment("// Pick the PC after the actual FLOW operation.");
        let flow_pc = push_muxer(back, &possible_flow_pcs, instr.op_label);
        // TODO: deal with the offset of flow opcodes rather than index in the muxer above.
        back.cost_est.print_cost();

        comment("// Execute possible MEM store and load operations.");
        let is_store = Self::push_is_mem_store(back, instr.op_label);
        if capab.possible_mem_store {
            mem.store(back, is_store, arg2, arg0);
        }
        let mem_result = if capab.possible_mem_load {
            let loaded = mem.load(back, arg2);
            push_muxer(back, &[loaded, copy_arg0], is_store)
        } else {
            copy_arg0
        };
        back.cost_est.print_cost();

        comment("// Pick the (result, flag, pc) after either the ALU or FLOW or MEM operation.");
        let op_type = Self::push_opcode_type(back, instr.op_label);

        let result = push_muxer(back, &[alu_result, copy_arg0, mem_result], op_type);
        let new_flag = push_muxer(back, &[alu_flag, copy_flag, copy_flag], op_type);
        let new_pc = push_muxer(back, &[next_pc, flow_pc, next_pc], op_type);

        comment("// Write the new state.");
        push_demuxer(back, &mut self.registers, instr.reg_label0, result);
        self.flag = new_flag;
        self.pc = new_pc;

        println!("pc = {:?}, flag = {:?}", new_pc, new_flag);
        back.cost_est.print_cost();
    }

    pub fn push_dynamic_instr_at_pc(&mut self, back: &mut PrototypeBackend, mem: &mut Memory, capab: &StepCapabilities) {
        comment("// Fetch and decode a dynamic instruction at pc.");
        let instr_at_pc = mem.load(back, self.pc);
        let instr = DynInstr::decode_instr(back, capab, instr_at_pc);
        back.cost_est.print_cost();
        self.push_dynamic_instr(back, mem, capab, &instr);
    }

    // Helpers.

    pub fn get_op_type(op: OpLabel) -> usize {
        if op < 12 { 0 } else if op < 12 + 4 { 1 } else { 2 } // TODO: use actual codes.
    }

    pub fn push_opcode_type(back: &mut PrototypeBackend, opcode: WireId) -> WireId {
        let _ = back.represent_as_one_hot(opcode);
        // TODO: decode "is alu", "is flow", "is mem".
        back.cost_est.cost += 2;
        let op_type = back.new_wire();
        println!("{:?}\t= opcode_type( {:?} )", op_type, opcode);
        op_type
    }

    pub fn push_is_mem_store(back: &mut PrototypeBackend, opcode: WireId) -> WireId {
        let _ = back.represent_as_one_hot(opcode);
        // TODO: decode "is store"
        back.cost_est.cost += 1;
        let is_store = back.new_wire();
        println!("{:?}\t= is_mem_store( {:?} )", is_store, opcode);
        is_store
    }

    pub fn push_increment_pc(back: &mut PrototypeBackend, pc: WireId) -> WireId {
        let _ = back.represent_as_field(pc);
        // TODO: pc + 1.
        back.cost_est.cost += 1;
        let next_pc = back.new_wire();
        println!("{:?}\t= increment_pc {:?}", next_pc, pc);
        next_pc
    }
}
