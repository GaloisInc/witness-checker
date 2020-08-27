use crate::back::zkif::zkif_cs::{WireRepr, WireId, Num, ZkifCS};
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
                // TODO: convert from other repr.
                Boolean::constant(false)
            }
        }
    }

    pub fn as_bellman_num(&mut self, wid: WireId) -> Num {
        let repr = &mut self.wire_reprs[wid.0];
        match &repr.bl_num {
            Some(lc) => lc.clone(),
            None => {
                // TODO: convert from other repr.
                let num = {
                    /*if let Some(ref int) = repr.bl_uint32 {
                        int_into_num(self, int)
                    } else {
                        Num::from_boolean::<Self>(&Boolean::constant(true))
                    }*/
                    Num::from_boolean::<ZkifCS>(&Boolean::constant(true))
                };
                repr.bl_num = Some(num.clone());
                num
            }
        }
    }

    pub fn as_bellman_uint32(&mut self, wid: WireId) -> UInt32 {
        let repr = &mut self.wire_reprs[wid.0];
        match &repr.bl_uint32 {
            Some(u) => u.clone(),
            None => {
                // TODO: convert from other repr.
                UInt32::constant(0)
            }
        }
    }
}