use zkinterface_bellman::bellman::gadgets::boolean::Boolean;
use super::{
    backend::{Num, CS},
    int::Int,
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
    pub num: Option<Num>,
    pub int: Option<Int>,
}

impl From<Num> for WireRepr {
    fn from(num: Num) -> Self {
        WireRepr { num: Some(num), ..Self::default() }
    }
}

impl From<Int> for WireRepr {
    fn from(int: Int) -> Self {
        WireRepr { int: Some(int), ..Self::default() }
    }
}

impl From<Boolean> for WireRepr {
    fn from(b: Boolean) -> Self {
        Self::from(Int::from_bits(&[b]))
    }
}

impl WireRepr {
    pub fn as_num(&mut self) -> Num {
        match &self.num {
            Some(num) => num.clone(),

            None => {
                // Convert from another repr.
                let num = {
                    if let Some(int) = &self.int {
                        Num::from_int::<CS>(int)
                    } else {
                        panic!("Access to a wire that has no representation")
                    }
                };
                self.num = Some(num.clone());
                num
            }
        }
    }

    /// Get `self` as a "truncated" num (as by `Num::truncate`), with `real_bits == valid_bits`.
    pub fn as_num_trunc(&mut self, cs: &mut CS) -> Num {
        let mut num = self.as_num();
        if num.valid_bits != num.real_bits {
            num = num.truncate(cs);
            self.num = Some(num.clone());
        }
        num
    }

    pub fn as_int(&mut self, cs: &mut CS, width: usize) -> Int {
        match &self.int {
            Some(u) => {
                // Currently we don't support treating the same `WireRepr` as multiple widths of
                // int - and anyway, it should never happen, since the width is set based on the
                // type of the wire.
                assert_eq!(u.width(), width);
                u.clone()
            }

            None => {
                // Convert from another repr.
                let int = {
                    if let Some(num) = &self.num {
                        Int::from_num(cs, width, num)
                    } else {
                        panic!("Access to a wire that has no representation")
                    }
                };
                self.int = Some(int.clone());
                int
            }
        }
    }

    pub fn as_boolean(&mut self, cs: &mut CS) -> Boolean {
        let i = self.as_int(cs, 1);
        assert!(i.bits.len() == 1);
        i.bits[0].clone()
    }
}
