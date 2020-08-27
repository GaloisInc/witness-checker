use crate::back::zkif::zkif_cs::{Num, ZkifCS};
use zkinterface_bellman::sapling_crypto::circuit::boolean::Boolean;
use crate::back::zkif::uint32::UInt32;


pub struct Representer {
    pub wire_reprs: Vec<WireRepr>,
}

impl Representer {
    pub fn new() -> Representer {
        Representer { wire_reprs: vec![] }
    }

    pub fn allocate_repr(&mut self) -> WireId {
        self.wire_reprs.push(WireRepr::default());
        WireId(self.wire_reprs.len() - 1)
    }

    pub fn mut_repr(&mut self, wid: WireId) -> &mut WireRepr {
        &mut self.wire_reprs[wid.0]
    }
}


// WireId is an handle to reference a wire in the backend.
#[derive(Copy, Clone, PartialEq)]
pub struct WireId(pub usize);

// WireRepr holds one or several equivalent representations of a wire.
#[derive(Default)]
pub struct WireRepr {
    pub boolean: Option<Boolean>,
    pub num: Option<Num>,
    pub uint32: Option<UInt32>,
}

impl WireRepr {
    pub fn set_boolean(&mut self, b: Boolean) {
        self.boolean = Some(b);
    }

    pub fn set_num(&mut self, num: Num) {
        num.assert_no_overflow();
        self.num = Some(num);
    }

    pub fn set_uint32(&mut self, u: UInt32) {
        self.uint32 = Some(u);
    }

    pub fn as_boolean(&mut self) -> Boolean {
        match &self.boolean {
            Some(b) => b.clone(),
            None => {
                panic!("Access to a wire that has no Boolean representation");
                // TODO: convert from other repr.
                Boolean::constant(true)
            }
        }
    }

    pub fn as_num(&mut self, cs: &mut ZkifCS) -> Num {
        match &self.num {
            Some(num) => num.clone(),

            None => {
                // Convert from another repr.
                let num = {
                    if let Some(b) = &self.boolean {
                        Num::from_boolean::<ZkifCS>(b)
                    } else if let Some(int) = &self.uint32 {
                        Num::from_int(cs, int)
                    } else {
                        panic!("Access to a wire that has no representation")
                    }
                };
                self.num = Some(num.clone());
                num
            }
        }
    }

    pub fn as_uint32(&mut self, cs: &mut ZkifCS) -> UInt32 {
        match &self.uint32 {
            Some(u) => u.clone(),

            None => {
                // Convert from another repr.
                let int = {
                    if let Some(b) = &self.boolean {
                        UInt32::from_boolean(b)
                    } else if let Some(num) = &self.num {
                        UInt32::from_num(cs, num)
                    } else {
                        panic!("Access to a wire that has no representation")
                    }
                };
                self.uint32 = Some(int.clone());
                int
            }
        }
    }
}

