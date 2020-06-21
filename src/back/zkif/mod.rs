mod backend;
mod machine;
mod mem;
mod debug;


#[test]
fn test_zkif_backend() {
    let mut back = backend::Backend::new();
    let mut state = machine::MachineState::new(&mut back);
    let mut mem = mem::Memory::new();
    let true_wire = back.true_wire();

    println!("Initial state: {:#?}", state);
    back.print_cost();
    println!();

    {
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
        let instr_in_pc = mem.load(&mut back, true_wire, state.pc);
        let instr = machine::SecretInstr::decode_instr(&mut back, instr_in_pc);

        state.push_secret_instr(&mut back, &capab, &instr);

        println!();
    }

    mem.finish(&mut back);
}

