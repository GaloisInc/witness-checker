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
        let instr = machine::FixedInstr {
            oplabel: 0,
            reglabel0: 0,
            reglabel1: 1,
            reglabel2: 2,
        };
        state.push_fixed_instr(&mut back, &instr);
        println!();
    }

    // A description of what a secret step may do.
    let capab = machine::StepCapabilities::new();

    for _ in 0..2 {
        state.push_secret_instr_at_pc(&mut back, &mut mem, &capab);

        println!();
    }

    mem.finish(&mut back);
}

