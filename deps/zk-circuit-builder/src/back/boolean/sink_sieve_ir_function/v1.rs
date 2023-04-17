use zki_sieve;
use zki_sieve::structs::function::Function;
use zki_sieve::structs::gates::Gate;
use zki_sieve::structs::instance::Instance;
use zki_sieve::structs::relation::Relation;
use zki_sieve::structs::wire::WireListElement;
use zki_sieve::structs::witness::Witness;
use crate::back::boolean::WireId;
use super::SieveIrFormat;
use super::VecSink;

#[derive(Debug, Default)]
pub struct SieveIrV1;

impl SieveIrFormat for SieveIrV1 {
    type Gate = Gate;
    type Function = Function;
    type Relation = Relation;
    type PublicInputs = Instance;
    type PrivateInputs = Witness;

    fn gate_constant(out: WireId, val: Vec<u8>) -> Gate {
        Gate::Constant(out, val)
    }
    fn gate_private(out: WireId) -> Gate {
        Gate::Witness(out)
    }
    fn gate_copy(out: WireId, a: WireId) -> Gate {
        Gate::Copy(out, a)
    }
    fn gate_and(out: WireId, a: WireId, b: WireId) -> Gate {
        Gate::And(out, a, b)
    }
    fn gate_xor(out: WireId, a: WireId, b: WireId) -> Gate {
        Gate::Xor(out, a, b)
    }
    fn gate_not(out: WireId, a: WireId) -> Gate {
        Gate::Not(out, a)
    }
    fn gate_new(start: WireId, end: WireId) -> Gate {
        unimplemented!()
    }
    fn gate_delete(start: WireId, end: WireId) -> Gate {
        if start == end {
            Gate::Free(start, None)
        } else {
            Gate::Free(start, Some(end))
        }
    }
    fn gate_call(
        name: String,
        outs: impl IntoIterator<Item = (WireId, WireId)>,
        ins: impl IntoIterator<Item = (WireId, WireId)>,
    ) -> Gate {
        Gate::Call(
            name,
            outs.into_iter().map(|(start, end)| {
                if start == end {
                    WireListElement::Wire(start)
                } else {
                    WireListElement::WireRange(start, end)
                }
            }).collect(),
            ins.into_iter().map(|(start, end)| {
                if start == end {
                    WireListElement::Wire(start)
                } else {
                    WireListElement::WireRange(start, end)
                }
            }).collect(),
        )
    }
    fn gate_assert_zero(w: WireId) -> Gate {
        Gate::AssertZero(w)
    }

    fn new_function(
        name: String,
        outs: impl IntoIterator<Item = u64>,
        ins: impl IntoIterator<Item = u64>,
        private_count: u64,
        gates: Vec<Gate>,
    ) -> Function {
        Function::new(
            name,
            outs.into_iter().sum::<u64>() as usize,
            ins.into_iter().sum::<u64>() as usize,
            // No public inputs consumed
            0,
            private_count as usize,
            gates,
        )
    }

    const HAS_PLUGINS: bool = false;

    fn new_plugin_function(
        _name: String,
        _outs: impl IntoIterator<Item = u64>,
        _ins: impl IntoIterator<Item = u64>,
        _plugin_name: String,
        _op_name: String,
        _args: Vec<String>,
    ) -> Function {
        panic!("plugins are not supported by this format")
    }

    fn relation_gate_count_approx(r: &Relation) -> usize {
        r.gates.len()
    }
    fn visit_relation(
        r: Relation,
        mut visit_gate: impl FnMut(Gate),
        mut visit_function: impl FnMut(Function),
    ) {
        for f in r.functions {
            visit_function(f);
        }
        for g in r.gates {
            visit_gate(g);
        }
    }
}


impl zki_sieve::Sink for VecSink<SieveIrV1> {
    type Write = Vec<u8>;

    fn get_instance_writer(&mut self) -> &mut Self::Write {
        unimplemented!()
    }
    fn get_witness_writer(&mut self) -> &mut Self::Write {
        unimplemented!()
    }
    fn get_relation_writer(&mut self) -> &mut Self::Write {
        unimplemented!()
    }

    fn push_instance_message(
        &mut self,
        instance: &Instance,
    ) -> zki_sieve_v3::Result<()> {
        self.public_inputs.push(instance.clone());
        Ok(())
    }

    fn push_witness_message(
        &mut self,
        witness: &Witness,
    ) -> zki_sieve_v3::Result<()> {
        self.private_inputs.push(witness.clone());
        Ok(())
    }

    fn push_relation_message(
        &mut self,
        relation: &Relation,
    ) -> zki_sieve_v3::Result<()> {
        self.relations.push(relation.clone());
        Ok(())
    }
}
