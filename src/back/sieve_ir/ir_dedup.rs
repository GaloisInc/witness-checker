use std::collections::hash_map::Entry::{Occupied, Vacant};
use std::collections::HashMap;
use std::mem::size_of;
use zki_sieve::producers::builder::{BuildGate, GateBuilderT};
use zki_sieve::WireId;
use BuildGate::*;

#[derive(Default)]
pub struct IRDedup {
    // NICE-TO-HAVE: LRU cache to save memory. Must be deterministic.
    gate_cache: HashMap<BuildGate, WireId>,
    hit_count: usize,
}

impl IRDedup {
    pub fn create_gate(&mut self, builder: &mut impl GateBuilderT, gate: BuildGate) -> WireId {
        // Don’t cache allocations.
        match gate {
            Instance(_) | Witness(_) => return builder.create_gate(gate),
            _ => {}
        };

        match self.gate_cache.entry(gate) {
            Occupied(entry) => {
                self.hit_count += 1;
                *entry.get()
            }
            Vacant(entry) => {
                let gate = entry.key().clone();
                let out_id = builder.create_gate(gate);
                entry.insert(out_id);
                out_id
            }
        }

        // Or one-liner without hit_count.
        // *self.gate_cache.entry(gate).or_insert_with_key(|gate| b.create_gate(gate.clone()))
    }

    pub fn print_report(&self) {
        // Wild estimate of HashMap size.
        let ram = self.gate_cache.capacity() * size_of::<(BuildGate, WireId, u64)>();
        eprintln!(
            "IRDedup removed {} duplicate gates using a cache of {} gates in ~{}MB of memory\n",
            self.hit_count,
            self.gate_cache.len(),
            ram / 1024 / 1024,
        );
    }
}
