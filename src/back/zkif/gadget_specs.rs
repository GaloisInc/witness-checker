use std::collections::HashMap;

pub struct GadgetSpec {
    inputs: Vec<GadgetConnection>,
    outputs: Vec<GadgetConnection>,
}

struct GadgetConnection {
    repr_kinds: Vec<ReprKind>
}

enum ReprKind {
    Packed(usize),
    Bits(usize),
    OneHot(usize),
}

impl GadgetSpec {
    pub fn make_specs() -> HashMap<String, GadgetSpec> {
        let mut specs = HashMap::new();

        specs.insert("cmp".to_owned(), GadgetSpec {
            inputs: vec![
                GadgetConnection { repr_kinds: vec![ReprKind::Packed(1)] },
                GadgetConnection { repr_kinds: vec![ReprKind::Packed(1)] },
            ],
            outputs: vec![
                GadgetConnection { repr_kinds: vec![ReprKind::Bits(1)] },
            ],
        });

        specs
    }
}


/*
GateKind::Gadget(gadget_kind, in_wires) => {
    let wire_ids: Vec<WireId> = in_wires.iter().map(|w| self.wire(*w)).collect();

    let gadget_spec = self.gadget_specs.get("cmp").unwrap();

    let mut input_vars = Vec::<u64>::new();

    self.wire_representer.push_zkif_vars(&mut input_vars, wire_ids[0], &gadget_spec.inputs[0]);

    eprintln!("{:?} (vars: {:?})", gate, input_vars);

    let gadget_input = CircuitOwned {
        connections: VariablesOwned {
            variable_ids: input_vars,
            values: None,
        },
        free_variable_id: self.wire_representer.stmt.vars.free_variable_id,
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
    let gadget_response = call_gadget_cb(&mut self.wire_representer.stmt, &gadget_input, &command).unwrap();

    let res_zkids = gadget_response.connections.variable_ids;
    self.wire_representer.wire_reprs[wid.0].packed_zid = Some(res_zkids[0]);
}


    fn push_zkif_vars(&mut self, input_vars: &mut Vec<u64>, wid: WireId, gadget_conn: &GadgetConnection) {
        for repr_kind in &gadget_conn.repr_kinds {
            match repr_kind {
                ReprKind::Packed(1) => {
                    let zkid = self.wire_as_field(wid);
                    input_vars.push(zkid);
                }
                ReprKind::Packed(_) => { unimplemented!("large packed input") }
                ReprKind::Bits(_) => { unimplemented!("bits input") }
                ReprKind::OneHot(_) => { unimplemented!("one-hot input") }
            }
        }
    }
*/