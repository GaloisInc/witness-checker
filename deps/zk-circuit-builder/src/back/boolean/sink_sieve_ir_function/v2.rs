use std::collections::HashMap;
use zki_sieve_v3;
use zki_sieve_v3::structs::count::Count;
use zki_sieve_v3::structs::directives::Directive;
use zki_sieve_v3::structs::function::{Function, FunctionBody};
use zki_sieve_v3::structs::gates::Gate;
use zki_sieve_v3::structs::plugin::PluginBody;
use zki_sieve_v3::structs::private_inputs::PrivateInputs;
use zki_sieve_v3::structs::public_inputs::PublicInputs;
use zki_sieve_v3::structs::relation::Relation;
use zki_sieve_v3::structs::types::Type;
use zki_sieve_v3::structs::wirerange::WireRange;
use crate::back::boolean::WireId;
use super::SieveIrFormat;
use super::VecSink;

#[derive(Debug, Default)]
pub struct SieveIrV2;

impl SieveIrFormat for SieveIrV2 {
    type Gate = Gate;
    type Function = Function;
    type Relation = Relation;
    type PublicInputs = PublicInputs;
    type PrivateInputs = PrivateInputs;

    fn gate_constant(out: WireId, val: Vec<u8>) -> Gate {
        Gate::Constant(0, out, val)
    }
    fn gate_private(out: WireId) -> Gate {
        Gate::Private(0, out)
    }
    fn gate_copy(out: WireId, a: WireId) -> Gate {
        Gate::Copy(0, out, a)
    }
    fn gate_and(out: WireId, a: WireId, b: WireId) -> Gate {
        Gate::Mul(0, out, a, b)
    }
    fn gate_xor(out: WireId, a: WireId, b: WireId) -> Gate {
        Gate::Add(0, out, a, b)
    }
    fn gate_not(out: WireId, a: WireId) -> Gate {
        Gate::AddConstant(0, out, a, vec![1])
    }
    fn gate_new(start: WireId, end: WireId) -> Gate {
        Gate::New(0, start, end)
    }
    fn gate_delete(start: WireId, end: WireId) -> Gate {
        Gate::Delete(0, start, end)
    }
    fn gate_call(
        name: String,
        outs: impl IntoIterator<Item = (WireId, WireId)>,
        ins: impl IntoIterator<Item = (WireId, WireId)>,
    ) -> Gate {
        Gate::Call(
            name,
            outs.into_iter().map(|(start, end)| WireRange::new(start, end)).collect(),
            ins.into_iter().map(|(start, end)| WireRange::new(start, end)).collect(),
        )
    }
    fn gate_assert_zero(w: WireId) -> Gate {
        Gate::AssertZero(0, w)
    }

    fn new_function(
        name: String,
        outs: impl IntoIterator<Item = u64>,
        ins: impl IntoIterator<Item = u64>,
        _private_count: u64,
        gates: Vec<Gate>,
    ) -> Function {
        Function::new(
            name,
            outs.into_iter().map(|n| Count::new(0, n)).collect(),
            ins.into_iter().map(|n| Count::new(0, n)).collect(),
            FunctionBody::Gates(gates),
        )
    }

    const HAS_PLUGINS: bool = true;

    fn new_plugin_function(
        name: String,
        outs: impl IntoIterator<Item = u64>,
        ins: impl IntoIterator<Item = u64>,
        plugin_name: String,
        op_name: String,
        args: Vec<String>,
    ) -> Function {
        let body = PluginBody {
            name: plugin_name,
            operation: op_name,
            params: args,
            public_count: HashMap::new(),
            private_count: HashMap::new(),
        };
        Function::new(
            name,
            outs.into_iter().map(|n| Count::new(0, n)).collect(),
            ins.into_iter().map(|n| Count::new(0, n)).collect(),
            FunctionBody::PluginBody(body),
        )
    }

    fn relation_gate_count_approx(r: &Relation) -> usize {
        r.directives.len()
    }
    fn visit_relation(
        r: Relation,
        mut visit_gate: impl FnMut(Gate),
        mut visit_function: impl FnMut(Function),
    ) {
        debug_assert_eq!(r.types, vec![Type::Field(vec![2])]);
        for d in r.directives {
            match d {
                Directive::Gate(g) => visit_gate(g),
                Directive::Function(f) => visit_function(f),
            }
        }
    }
}


impl zki_sieve_v3::Sink for VecSink<SieveIrV2> {
    type Write = Vec<u8>;

    fn get_public_inputs_writer(
        &mut self,
        type_value: Type,
    ) -> zki_sieve_v3::Result<&mut Self::Write> {
        unimplemented!()
    }
    fn get_private_inputs_writer(
        &mut self,
        type_value: Type,
    ) -> zki_sieve_v3::Result<&mut Self::Write> {
        unimplemented!()
    }
    fn get_relation_writer(&mut self) -> &mut Self::Write {
        unimplemented!()
    }

    fn push_public_inputs_message(
        &mut self,
        public_inputs: &PublicInputs,
    ) -> zki_sieve_v3::Result<()> {
        self.public_inputs.push(public_inputs.clone());
        Ok(())
    }

    fn push_private_inputs_message(
        &mut self,
        private_inputs: &PrivateInputs,
    ) -> zki_sieve_v3::Result<()> {
        self.private_inputs.push(private_inputs.clone());
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
