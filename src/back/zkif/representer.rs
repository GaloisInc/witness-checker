use crate::back::zkif::zkif_cs::{Num, ZkifCS};
use zkinterface_bellman::sapling_crypto::circuit::boolean::Boolean;
use crate::back::zkif::uint32::UInt32;


// WireId is an handle to reference a wire in the backend.
#[derive(Copy, Clone, PartialEq)]
pub struct WireId(pub usize);

// WireRepr holds one or several equivalent representations of a wire.
#[derive(Default)]
pub struct WireRepr {
    pub bl_boolean: Option<Boolean>,
    pub bl_num: Option<Num>,
    pub bl_uint32: Option<UInt32>,
    //pub packed_zid: Option<ZkifId>,
    //pub bit_zids: Vec<ZkifId>,
    //pub one_hot_zids: Vec<ZkifId>,
}


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

    pub fn set_bellman_boolean(&mut self, wid: WireId, b: Boolean) {
        self.wire_reprs[wid.0].bl_boolean = Some(b);
    }

    pub fn set_bellman_num(&mut self, wid: WireId, num: Num) {
        num.assert_no_overflow();
        self.wire_reprs[wid.0].bl_num = Some(num);
    }

    pub fn set_bellman_uint32(&mut self, wid: WireId, u: UInt32) {
        self.wire_reprs[wid.0].bl_uint32 = Some(u);
    }

    pub fn as_bellman_boolean(&mut self, wid: WireId) -> Boolean {
        let repr = &mut self.wire_reprs[wid.0];
        match &repr.bl_boolean {
            Some(b) => b.clone(),
            None => {
                panic!("Access to a wire that has no Boolean representation");
                // TODO: convert from other repr.
                Boolean::constant(true)
            }
        }
    }

    pub fn as_bellman_num(&mut self, wid: WireId, cs: &mut ZkifCS) -> Num {
        let repr = &mut self.wire_reprs[wid.0];
        match &repr.bl_num {
            Some(num) => num.clone(),

            None => {
                // Convert from another repr.
                let num = {
                    if let Some(ref bool) = repr.bl_boolean {
                        Num::from_boolean::<ZkifCS>(bool)
                    } else if let Some(ref int) = repr.bl_uint32 {
                        Num::from_int(cs, int)
                    } else {
                        panic!("Access to a wire that has no representation")
                    }
                };
                repr.bl_num = Some(num.clone());
                num
            }
        }
    }

    pub fn as_bellman_uint32(&mut self, wid: WireId, cs: &mut ZkifCS) -> UInt32 {
        let repr = &mut self.wire_reprs[wid.0];
        match &repr.bl_uint32 {
            Some(u) => u.clone(),

            None => {
                // Convert from another repr.
                let int = {
                    if let Some(ref bool) = repr.bl_boolean {
                        UInt32::from_boolean(bool)
                    } else if let Some(ref num) = repr.bl_num {
                        UInt32::from_num(cs, num)
                    } else {
                        panic!("Access to a wire that has no representation")
                    }
                };
                repr.bl_uint32 = Some(int.clone());
                int
            }
        }
    }
}
