use super::backend::{Backend, WireId};

use std::collections::HashMap;

pub struct Memory {
    ops: Vec<MemOp>,
    values: HashMap<PackedValue, PackedValue>,
    finished: bool,
}

enum MemOp {
    Store { condition: WireId, address: WireId, content: WireId },
    Load { condition: WireId, address: WireId, content: WireId },
}

pub type PackedValue = [u64; 4];

impl Memory {
    pub fn new() -> Memory {
        Memory { ops: vec![], values: HashMap::new(), finished: false }
    }
    pub fn finish(mut self, back: &mut Backend) {
        // TODO: store/load consistency check.
        self.finished = true;
    }

    pub fn store(&mut self, condition: WireId, address: WireId, content: WireId) {
        self.ops.push(MemOp::Store { condition, address, content });
        // TODO: conditionally store the content.
        if false {
            self.values.insert([0, 0, 0, 0], [0, 0, 0, 0]);
        }
    }

    pub fn load(&mut self, back: &mut Backend, condition: WireId, address: WireId) -> WireId {
        let content = back.new_wire();
        self.ops.push(MemOp::Load { condition, address, content });
        // TODO: copy values[addr] into the new wire.
        return content;
    }
}

impl Drop for Memory {
    fn drop(&mut self) {
        if !self.finished {
            panic!("Memory.finish() must be called.");
        }
    }
}