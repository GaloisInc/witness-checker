use zk_circuit_builder::ir::migrate::{self, Migrate};

#[derive(Debug, Migrate)]
pub struct PanicOnDrop {
    defused: bool,
}

impl PanicOnDrop {
    pub fn new() -> PanicOnDrop {
        PanicOnDrop { defused: false }
    }

    pub fn defuse(&mut self) {
        self.defused = true;
    }
}

impl Drop for PanicOnDrop {
    fn drop(&mut self) {
        assert!(self.defused, "dropped a PanicOnDrop without defusing it first");
    }
}
