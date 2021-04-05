use std::collections::hash_map::Entry::{Occupied, Vacant};
use std::collections::HashMap;
use std::mem::size_of;
use zki_sieve::producers::builder::{BuildGate, GateBuilder, GateBuilderT};
use zki_sieve::{Sink, WireId};
use BuildGate::*;

pub struct IRCache<S: Sink> {
    pub b: GateBuilder<S>,

    // NICE-TO-HAVE: LRU cache to save memory.
    gate_cache: HashMap<BuildGate, WireId>,
    hit_count: usize,
}

impl<S: Sink> GateBuilderT for IRCache<S> {
    fn create_gate(&mut self, gate: BuildGate) -> WireId {
        let b = &mut self.b;

        // Don’t cache allocations.
        match gate {
            Instance(_) | Witness(_) => return b.create_gate(gate),
            _ => {}
        };

        match self.gate_cache.entry(gate) {
            Occupied(entry) => {
                self.hit_count += 1;
                *entry.get()
            }
            Vacant(entry) => {
                let gate = entry.key().clone();
                let out_id = b.create_gate(gate);
                entry.insert(out_id);
                out_id
            }
        }

        // Or one-liner without hit_count.
        // *self.gate_cache.entry(gate).or_insert_with_key(|gate| b.create_gate(gate.clone()))
    }
}

impl<S: Sink> IRCache<S> {
    pub fn new(builder: GateBuilder<S>) -> Self {
        Self {
            b: builder,
            gate_cache: Default::default(),
            hit_count: 0,
        }
    }

    pub fn finish(self) -> S {
        self.b.finish()
    }

    pub fn print_report(&self) {
        let ram = self.gate_cache.capacity() * size_of::<(BuildGate, WireId, u64)>();
        eprintln!(
            "IRCache: size {} gates, ~{}MB memory, {} hits\n",
            self.gate_cache.len(),
            ram / 1024 / 1024,
            self.hit_count,
        );
    }
}
