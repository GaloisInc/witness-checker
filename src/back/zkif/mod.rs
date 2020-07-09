use crate::back::zkif::machine::RegOrValue;

mod backend;
mod machine;
mod mem;
mod debug;

//#[cfg(feature = "libsnark")]

use zkinterface::{
    statement::{StatementBuilder, FileStore},
    Result,
};

#[test]
fn test_zkif_backend() -> Result<()> {
    let out_path = "local/test_statement_public_";
    let store = FileStore::new(out_path, true, false, true)?;
    let stmt = StatementBuilder::new(store);

    let mut back = backend::Backend::new(stmt);
    let mut state = machine::MachineState::new(&mut back);
    let mut mem = mem::Memory::new();

    println!("\nInitial state: {:#?}\n", state);

    for _ in 0..2 {
        let instr = machine::StaticInstr {
            op_label: 0,
            reg_label0: 0,
            reg_label1: 1,
            reg_label2: RegOrValue::Val([2, 3, 4, 5]),
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

    println!("Written {}*.zkif", out_path);
    Ok(())
}
