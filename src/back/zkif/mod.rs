use crate::back::zkif::machine::RegOrValue;

pub mod backend;
mod prototype_backend;
mod gadgetlib;
mod machine;
mod mem;
mod debug;

use zkinterface::{
    statement::{StatementBuilder, Store, FileStore},
    Result,
    CircuitOwned, VariablesOwned, KeyValueOwned,
};

#[test]
fn test_zkif_backend() -> Result<()> {
    let out_path = "local/test_statement";
    let store = FileStore::new(out_path, true, true, true)?;
    let stmt = StatementBuilder::new(store);

    let mut back = prototype_backend::PrototypeBackend::new(stmt);
    let mut state = machine::MachineState::new(&mut back);
    let mut mem = mem::Memory::new();

    println!("\nInitial state: {:#?}\n", state);

    for _ in 0..2 {
        let instr = machine::StaticInstr {
            op_label: 0,
            reg_label0: 0,
            reg_label1: 1,
            reg_label2: RegOrValue::Reg(2),
        };
        state.push_static_instr(&mut back, &mut mem, &instr);
        println!();
    }

    // A description of what a dynamic step may do.
    let capab = machine::StepCapabilities::new();

    for _ in 0..2 {
        state.push_dynamic_instr_at_pc(&mut back, &mut mem, &capab);

        println!();
    }

    println!("// Final memory consistency check.");
    mem.finish(&mut back);
    back.cost_est.print_cost();

    let main = CircuitOwned {
        connections: VariablesOwned {
            variable_ids: vec![],
            values: Some(vec![]),
        },
        free_variable_id: back.stmt.vars.free_variable_id,
        field_maximum: None,
        configuration: Some(vec![
            KeyValueOwned {
                key: "function".to_string(),
                text: Some("main.test_statement".to_string()),
                data: None,
                number: 0,
            }]),
    };
    back.stmt.store.push_main(&main)?;

    println!("Written {}/*.zkif", out_path);
    Ok(())
}
