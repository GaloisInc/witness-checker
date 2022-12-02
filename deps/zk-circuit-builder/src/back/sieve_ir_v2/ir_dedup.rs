use std::collections::hash_map::Entry::{Occupied, Vacant};
use std::collections::{HashMap, VecDeque};
use std::mem::size_of;
use zki_sieve_v3::producers::builder::{BuildGate, GateBuilderT};
use BuildGate::*;
use crate::back::sieve_ir_v2::ir_builder::{IRWire, Deleted};

/// IRDedup deduplicates gates. When the caller attempts to create a gate,
///   - either create a new gate and return a fresh WireId,
///   - or return an existing WireId allocated for a prior equivalent gate.
///
/// IRDedup maintains a cache of gates and WireIds with a bound on memory usage.
/// It uses a FIFO queue to make it clear how it is deterministic:
/// when the cache is full, it evicts the oldest gate in order of insertion.
// NICE-TO-HAVE: this could use a LRU, as long as its behavior is clear and stable.
#[derive(Default)]
pub struct IRDedup {
    gate_cache: HashMap<BuildGate, IRWire>,
    gate_queue: VecDeque<BuildGate>,
    hit_count: usize,
}

impl IRDedup {
    /// Maximum number of gates to store in the deduplication cache.
    /// The result is deterministic for a given MAX_SIZE.
    ///
    /// WARNING: it is recommended to stick with a fixed MAX_SIZE because this affects
    /// the exact relation being generated. Don't tune it at runtime.
    ///
    /// This should take maybe 100-200MB of memory per million of gates.
    /// Default: 1M gates.
    pub const MAX_SIZE: usize = 2 * 1000 * 1000;

    pub fn create_gate(&mut self, builder: &mut impl GateBuilderT, gate: BuildGate, freed: Deleted) -> IRWire {
        // Don't cache allocations.
        match gate {
            Public(_, _) | Private(_, _) =>
                return IRWire::new(builder.create_gate(gate).unwrap(), freed),
            _ => {}
        };

        let queue = &mut self.gate_queue;

        match self.gate_cache.entry(gate) {
            Occupied(entry) => {
                // Return cached gate.
                self.hit_count += 1;
                entry.get().clone()
            }
            Vacant(entry) => {
                // Build the new gate.
                let gate = entry.key();
                let out_id = IRWire::new(builder.create_gate(gate.clone()).unwrap(), freed);

                // Insert the new gate in the cache.
                queue.push_back(gate.clone());
                entry.insert(out_id.clone());

                // Remove the oldest gate to limit size.
                if queue.len() >= Self::MAX_SIZE {
                    let to_remove = queue.pop_front().unwrap();
                    self.gate_cache.remove(&to_remove).unwrap();
                }

                out_id
            }
        }
    }

    pub fn print_report(&self) {
        // Wild estimate of HashMap size.
        let ram = self.gate_cache.capacity() * size_of::<(BuildGate, IRWire, u64)>()
            + self.gate_queue.capacity() * size_of::<BuildGate>();

        eprintln!(
            "IRDedup removed {} duplicate gates using a cache of {} gates in ~{}MB of memory\n",
            self.hit_count,
            self.gate_cache.len(),
            ram / 1024 / 1024,
        );
    }
}
