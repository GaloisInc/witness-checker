use super::{backend::Num, boolean::Boolean, int::Int, ir_builder::IRBuilderT};

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

// WireRepr holds one or several equivalent representations of an abstract wire as zki_sieve wires.
#[derive(Default)]
pub struct WireRepr {
    pub num: Option<Num>,
    pub int: Option<Int>,
}

impl From<Num> for WireRepr {
    fn from(num: Num) -> Self {
        WireRepr {
            num: Some(num),
            ..Self::default()
        }
    }
}

impl From<Int> for WireRepr {
    fn from(int: Int) -> Self {
        WireRepr {
            int: Some(int),
            ..Self::default()
        }
    }
}

impl From<(Num, Int)> for WireRepr {
    fn from((num, int): (Num, Int)) -> Self {
        WireRepr {
            num: Some(num),
            int: Some(int),
        }
    }
}

impl From<Boolean> for WireRepr {
    fn from(b: Boolean) -> Self {
        Self::from(Int::from_bits(&[b]))
    }
}

impl WireRepr {
    pub fn as_num(&mut self, b: &mut impl IRBuilderT) -> Num {
        b.annotate("WireRepr::as_num");

        let num = match self.num {
            Some(ref num) => (*num).clone(),

            None => {
                // Convert from another repr.
                let num = {
                    if let Some(int) = &self.int {
                        Num::from_int(b, int)
                    } else {
                        panic!("Access to a wire that has no representation")
                    }
                };
                self.num = Some(num.clone());
                num
            }
        };
        b.deannotate();
        num
    }

    /// Get `self` as a "truncated" num (as by `Num::truncate`), with `real_bits == valid_bits`.
    pub fn as_num_trunc(&mut self, b: &mut impl IRBuilderT, width: usize) -> Num {
        b.annotate("WireRepr::as_num_trunc");

        // Maybe we have a truncated Num already.
        if let Some(ref num) = self.num {
            assert_eq!(
                num.valid_bits as usize, width,
                "multiple bit widths for a wire is not supported"
            );
            if num.is_truncated() {
                b.deannotate();
                return (*num).clone();
            }
        }

        // Otherwise we need an Int representation.
        // Maybe we have it in self.int already, otherwise build it from self.num.
        let int = self.as_int(b, width);

        let trunc_num = Num::from_int(b, &int);
        self.num = Some(trunc_num.clone());

        b.deannotate();
        trunc_num
    }

    pub fn as_int(&mut self, b: &mut impl IRBuilderT, width: usize) -> Int {
        b.annotate(&format!("WireRepr::as_int({})", width));

        let int = match &self.int {
            Some(u) => {
                // Currently we don't support treating the same `WireRepr` as multiple widths of
                // int - and anyway, it should never happen, since the width is set based on the
                // type of the wire.
                assert_eq!(
                    u.width(),
                    width,
                    "multiple bit widths for a wire is not supported"
                );
                u.clone()
            }

            None => {
                // Convert from another repr.
                let int = {
                    if let Some(num) = &self.num {
                        Int::from_num(b, width, num)
                    } else {
                        panic!("Access to a wire that has no representation")
                    }
                };
                self.int = Some(int.clone());
                int
            }
        };
        b.deannotate();
        int
    }

    pub fn as_boolean(&mut self, b: &mut impl IRBuilderT) -> Boolean {
        let i = self.as_int(b, 1);
        assert!(i.bits.len() == 1);
        i.bits[0].clone()
    }

    pub fn deallocate(&mut self) {
        if let Some(int) = &self.int {
            drop(int);
        }
        self.int = None;
        if let Some(num) = &self.num {
            drop(num);
        }
        self.num = None;
    }
}
