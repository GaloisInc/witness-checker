
#[test]
fn test_gadgetlib() {
    use zkinterface::owned::{
        variables::VariablesOwned,
        circuit::CircuitOwned,
        command::CommandOwned,
    };
    use zkinterface_libsnark::gadgetlib::call_gadget;

    let mut subcircuit = CircuitOwned {
        connections: VariablesOwned {
            variable_ids: vec![100, 101, 102, 103], // Some input variables.
            values: None,
        },
        free_variable_id: 104,
        field_maximum: None,
    };


    println!("==== R1CS generation ====");
    let command = CommandOwned { constraints_generation: true, witness_generation: false };
    let r1cs_response = call_gadget(&subcircuit, &command).unwrap();

    println!("R1CS: Rust received {} messages including {} gadget return.",
             r1cs_response.messages.len(),
             r1cs_response.circuits().len());

    assert!(r1cs_response.messages.len() == 2);
    assert!(r1cs_response.circuits().len() == 1);

    println!("R1CS: Got constraints:");
    for c in r1cs_response.iter_constraints() {
        println!("{:?} * {:?} = {:?}", c.a, c.b, c.c);
    }

    let free_variable_id_after = r1cs_response.last_circuit().unwrap().free_variable_id();
    println!("R1CS: Free variable id after the call: {}\n", free_variable_id_after);
    assert!(free_variable_id_after == 104 + 36);


    println!("==== Witness generation ====");
    // Specify input values.
    subcircuit.connections.values = Some(vec![11, 12, 9, 14 as u8]);

    let command = CommandOwned { constraints_generation: false, witness_generation: true };
    let witness_response = call_gadget(&subcircuit, &command).unwrap();

    println!("Assignment: Rust received {} messages including {} gadget return.",
             witness_response.messages.len(),
             witness_response.circuits().len());

    assert!(witness_response.messages.len() == 2);
    assert!(witness_response.circuits().len() == 1);

    {
        let assignment: Vec<_> = witness_response.iter_witness().collect();

        println!("Assignment: Got witness:");
        for var in assignment.iter() {
            println!("{:?}", var);
        }

        assert_eq!(assignment.len(), 36);
        assert_eq!(assignment[0].id, 104 + 0); // First gadget-allocated variable.
        assert_eq!(assignment[0].value.len(), 32);
        assert_eq!(assignment[1].id, 104 + 1); // Second "
        assert_eq!(assignment[1].value.len(), 32);

        let free_variable_id_after2 = witness_response.last_circuit().unwrap().free_variable_id();
        println!("Assignment: Free variable id after the call: {}", free_variable_id_after2);
        assert!(free_variable_id_after2 == free_variable_id_after);

        let out_vars = witness_response.connection_variables().unwrap();
        println!("Output variables: {:?}", out_vars);
        assert_eq!(out_vars.len(), 2);
    }
    println!();
}
