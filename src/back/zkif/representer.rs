use zkinterface_bellman::sapling_crypto::circuit::boolean::Boolean;
use super::{
    zkif_cs::{Num, ZkifCS},
    int32::Int32,
};


pub struct Representer {
    pub wire_reprs: Vec<WireRepr>,
}

impl Representer {
    pub fn new() -> Representer {
        Representer { wire_reprs: vec![] }
    }

    pub fn new_repr(&mut self, repr: WireRepr) -> ReprId {
        self.wire_reprs.push(repr);
        ReprId(self.wire_reprs.len() - 1)
    }

    pub fn mut_repr(&mut self, wid: ReprId) -> &mut WireRepr {
        &mut self.wire_reprs[wid.0]
    }
}


// ReprId is a reference to a wire representation.
#[derive(Copy, Clone, PartialEq)]
pub struct ReprId(pub usize);

// WireRepr holds one or several equivalent representations of a wire.
#[derive(Default)]
pub struct WireRepr {
    pub boolean: Option<Boolean>,
    pub num: Option<Num>,
    pub int32: Option<Int32>,
}

impl From<Boolean> for WireRepr {
    fn from(bool: Boolean) -> Self {
        WireRepr { boolean: Some(bool), ..Self::default() }
    }
}

impl From<Num> for WireRepr {
    fn from(num: Num) -> Self {
        WireRepr { num: Some(num), ..Self::default() }
    }
}

impl From<Int32> for WireRepr {
    fn from(int: Int32) -> Self {
        WireRepr { int32: Some(int), ..Self::default() }
    }
}

impl WireRepr {
    pub fn as_boolean(&mut self) -> Boolean {
        match &self.boolean {
            Some(b) => b.clone(),
            None => {
                panic!("Access to a wire that has no Boolean representation");
            }
        }
    }

    pub fn as_num(&mut self) -> Num {
        match &self.num {
            Some(num) => num.clone(),

            None => {
                // Convert from another repr.
                let num = {
                    if let Some(b) = &self.boolean {
                        Num::from_boolean::<ZkifCS>(b)
                    } else if let Some(int) = &self.int32 {
                        Num::from_int::<ZkifCS>(int)
                    } else {
                        panic!("Access to a wire that has no representation")
                    }
                };
                self.num = Some(num.clone());
                num
            }
        }
    }

    pub fn as_int32(&mut self, cs: &mut ZkifCS) -> Int32 {
        match &self.int32 {
            Some(u) => u.clone(),

            None => {
                // Convert from another repr.
                let int = {
                    if let Some(b) = &self.boolean {
                        Int32::from_boolean(b)
                    } else if let Some(num) = &self.num {
                        Int32::from_num(cs, num)
                    } else {
                        panic!("Access to a wire that has no representation")
                    }
                };
                self.int32 = Some(int.clone());
                int
            }
        }
    }
}

