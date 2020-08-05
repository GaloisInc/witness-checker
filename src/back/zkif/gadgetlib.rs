/// Core execution units.

use std::fmt;
use zkinterface::{
    owned::{circuit::CircuitOwned, variables::VariablesOwned, keyvalue::KeyValueOwned, command::CommandOwned},
    statement::{StatementBuilder, Store, FileStore},
    Result,
};
use zkinterface_libsnark::gadgetlib::call_gadget_cb;
use super::backend::{Backend, OpLabel, WireId};

// Add a stateless Arithmetic & Logic Unit:
//   new result and flag = operation( arg0, arg1, arg2 )
pub fn push_alu_op(back: &mut Backend, opcode: OpLabel, arg0: WireId, arg1: WireId, arg2: WireId) -> (WireId, WireId) {
    // TODO: use represent_as_bits instead.
    let arg0_var = back.represent_as_field(arg0);
    let arg1_var = back.represent_as_field(arg1);
    let arg2_var = back.represent_as_field(arg2);
    let flag = 0; // Flag unused.

    // Call the gadget for the given opcode using the wire representations.
    let input_vars = VariablesOwned {
        variable_ids: vec![arg0_var, arg1_var, arg2_var, flag],
        values: None,
    };
    let gadget_input = CircuitOwned {
        connections: input_vars.clone(),
        free_variable_id: back.stmt.vars.free_variable_id,
        field_maximum: None,
        configuration: Some(vec![
            KeyValueOwned {
                key: "function".to_string(),
                text: Some("tinyram.and".to_string()),
                data: None,
                number: 0,
            }]),
    };
    let command = CommandOwned { constraints_generation: true, witness_generation: true };
    let gadget_response = call_gadget_cb(&mut back.stmt, &gadget_input, &command).unwrap();

    back.cost_est.cost += 30;
    let new_res = back.new_wire_from_packed(gadget_response.connections.variable_ids[0]);
    let new_flag = back.new_wire_from_packed(gadget_response.connections.variable_ids[1]);

    println!("{:?}\t= alu_op_{}( {:?}, {:?}, {:?})", (new_res, new_flag), opcode, arg0, arg1, arg2);
    return (new_res, new_flag);
}

// Add a stateless Flow Control Unit:
//   new pc = operation( flag, pc, arg2 )
pub fn push_flow_op(back: &mut Backend, opcode: OpLabel, flag: WireId, pc: WireId, arg2: WireId) -> WireId {
    let _ = back.represent_as_field(flag);
    let _ = back.represent_as_field(pc);
    let _ = back.represent_as_field(arg2);

    // TODO: call the gadget for the given opcode using the wire representations.
    back.cost_est.cost += 4;
    let new_pc = back.new_wire();

    println!("{:?}\t= flow_op_{}( {:?}, {:?}, {:?} )", new_pc, opcode, pc, flag, arg2);
    return new_pc;
}

// Select one of multiple inputs at a secret index:
//   new wire = inputs[index]
// Or 0 if out-of-range.
pub fn push_muxer(back: &mut Backend, inputs: &[WireId], index: WireId) -> WireId {
    for w in inputs {
        let _ = back.represent_as_field(*w);
    }
    let _ = back.represent_as_one_hot(index);

    // TODO: call the muxer gadget.
    back.cost_est.cost += inputs.len();
    let mux_out = back.new_wire();

    println!("{:?}\t= muxer selects {:?} from {:?}", mux_out, index, inputs);
    return mux_out;
}

// Like push_muxer for pairs of wires accessed with the same secret index:
//   new wire tuple = input_tuples[index]
pub fn push_muxer_pair(back: &mut Backend, inputs: &[(WireId, WireId)], index: WireId) -> (WireId, WireId) {
    for (wa, wb) in inputs {
        let _ = back.represent_as_field(*wa);
        let _ = back.represent_as_field(*wb);
    }
    let _ = back.represent_as_one_hot(index);

    // TODO: call the muxer gadget.
    back.cost_est.cost += inputs.len() * 2;
    let mux_out = (back.new_wire(), back.new_wire());

    println!("{:?}\t= muxer selects {:?} from {:?}", mux_out, index, inputs);
    return mux_out;
}

// Update one of multiple registers at a secret index:
//   registers[index] = new wire equal to new_value.
// Unchanged registers are replaced by copies of their values:
//   registers[i != index] = new wire equal to the old value.
pub fn push_demuxer(back: &mut Backend, registers: &mut [WireId], index: WireId, new_value: WireId) {
    for w in &registers[..] {
        let _ = back.represent_as_field(*w);
    }
    let _ = back.represent_as_one_hot(index);
    let _ = back.represent_as_field(new_value);

    // TODO: call the demuxer gadget.
    back.cost_est.cost += registers.len();
    for i in 0..registers.len() {
        registers[i] = back.new_wire();
    }

    println!("regs[{:?}]\t= {:?} in new registers {:?}", index, new_value, registers);
}
