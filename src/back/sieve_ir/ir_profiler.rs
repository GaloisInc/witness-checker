use std::collections::HashMap;
use zki_sieve::producers::builder::{BuildGate, GateBuilderT};

pub struct IRProfiler<B: GateBuilderT> {
    pub b: B,

    gates: HashMap<BuildGate, ()>,

    pub gate_count: usize,
    pub duplicate_count: usize,
}

impl<B: GateBuilderT> GateBuilderT for IRProfiler<B> {
    fn create_gate(&mut self, gate: BuildGate) -> u64 {
        self.notify_gate(&gate);
        self.b.create_gate(gate)
    }
}

impl<B: GateBuilderT> IRProfiler<B> {
    pub fn new(builder: B) -> Self {
        Self {
            b: builder,
            gates: Default::default(),
            gate_count: 0,
            duplicate_count: 0,
        }
    }

    fn notify_gate(&mut self, gate: &BuildGate) {
        self.gate_count += 1;
        let previous = self.gates.insert(gate.clone(), ());
        if previous.is_some() {
            self.duplicate_count += 1;
        }
    }

    pub fn print_report(&self) {
        println!(
            "IRProfiler found {} duplicates out of {} total gates",
            self.duplicate_count, self.gate_count
        );
    }
}
