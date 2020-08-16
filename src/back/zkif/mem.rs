use super::prototype_backend::{PrototypeBackend, WireId, PackedValue};

use std::collections::HashMap;

pub struct Memory {
    ops: Vec<MemOp>,
    values: HashMap<PackedValue, PackedValue>,
    finished: bool,
}

enum MemOp {
    Store { condition: WireId, address: WireId, content: WireId },
    Load { address: WireId, content: WireId },
}

impl Memory {
    pub fn new() -> Memory {
        Memory { ops: vec![], values: HashMap::new(), finished: false }
    }

    pub fn finish(mut self, back: &mut PrototypeBackend) {
        // TODO: store/load consistency check.
        self.finished = true;
        back.cost_est.cost += self.ops.len() * 300;
    }

    pub fn store(&mut self, back: &mut PrototypeBackend, condition: WireId, address: WireId, content: WireId) {
        let _ = back.represent_as_field(condition);
        let _ = back.represent_as_bits(address);
        let _ = back.represent_as_field(content);

        self.ops.push(MemOp::Store { condition, address, content });

        // TODO: conditionally store the content.
        if false {
            self.values.insert([0, 0, 0, 0], [0, 0, 0, 0]);
        }

        println!("memory[{:?}]\t= {:?}\t{}", address, content,
                 if condition == back.wire_one() { "".to_string() } else { format!("( if {:?} )", condition) });
    }

    pub fn load(&mut self, back: &mut PrototypeBackend, address: WireId) -> WireId {
        let content = back.new_wire();

        let _ = back.represent_as_bits(address);
        let _ = back.represent_as_field(content);

        self.ops.push(MemOp::Load { address, content });

        // TODO: copy values[addr] into the new wire.
        println!("{:?}\t= memory[{:?}]", content, address);
        content
    }
}

impl Drop for Memory {
    fn drop(&mut self) {
        if !self.finished {
            panic!("Memory.finish() must be called.");
        }
    }
}