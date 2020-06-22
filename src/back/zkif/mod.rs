use crate::back::zkif::machine::RegOrValue;

mod backend;
mod machine;
mod mem;
mod debug;


#[test]
fn test_zkif_backend() {
    let mut back = backend::Backend::new();
    let mut state = machine::MachineState::new(&mut back);
    let mut mem = mem::Memory::new();
    let wire_true = back.wire_one();

    println!("\nInitial state: {:#?}\n", state);

    for _ in 0..2 {
        let instr = machine::StaticInstr {
            oplabel: 0,
            reglabel0: 0,
            reglabel1: 1,
            reglabel2: RegOrValue::Val([2, 3, 4, 5]),
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

    mem.finish(&mut back);
}
