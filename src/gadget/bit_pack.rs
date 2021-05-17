use crate::ir::circuit::{Circuit, CircuitTrait, Wire, Ty, TyKind, IntSize, GadgetKind, GadgetKindRef};
use crate::ir::typed::{Builder, TWire, Flatten};

struct BundleTys<'a> {
    stk: Vec<Ty<'a>>,
}

fn bundle_tys<'a>(tys: &[Ty<'a>]) -> BundleTys<'a> {
    BundleTys { stk: tys.iter().rev().cloned().collect() }
}

impl<'a> Iterator for BundleTys<'a> {
    type Item = Ty<'a>;
    fn next(&mut self) -> Option<Ty<'a>> {
        while let Some(ty) = self.stk.pop() {
            match *ty {
                TyKind::Bundle(tys) => {
                    self.stk.extend(tys.iter().rev().cloned());
                },
                TyKind::Uint(_) | TyKind::Int(_) => return Some(ty),
            }
        }
        None
    }
}

struct BundleWires<'c, 'a> {
    c: &'c Circuit<'a>,
    stk: Vec<Wire<'a>>,
}

fn bundle_wires<'c, 'a>(c: &'c Circuit<'a>, ws: &[Wire<'a>]) -> BundleWires<'c, 'a> {
    BundleWires { c, stk: ws.iter().rev().cloned().collect() }
}

impl<'a> Iterator for BundleWires<'_, 'a> {
    type Item = Wire<'a>;
    fn next(&mut self) -> Option<Wire<'a>> {
        while let Some(w) = self.stk.pop() {
            match *w.ty {
                TyKind::Bundle(tys) => {
                    let c = self.c;
                    self.stk.extend((0 .. tys.len()).rev().map(|i| c.extract(w, i)));
                },
                TyKind::Uint(_) | TyKind::Int(_) => return Some(w),
            }
        }
        None
    }
}

/// Concatenate the bits of all inputs into a single large `Uint`.  Takes any number of inputs.
/// Inputs of `Bundle` type will be processed recursively.  Inputs are concatenated in
/// little-endian order - the first input occupies the lowest bits of the output.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct ConcatBits;
impl_gadget_kind_support!(ConcatBits);

impl<'a> GadgetKind<'a> for ConcatBits {
    fn transfer<'b>(&self, c: &Circuit<'b>) -> GadgetKindRef<'b> {
        c.intern_gadget_kind(self.clone())
    }

    fn typecheck(&self, c: &Circuit<'a>, arg_tys: &[Ty<'a>]) -> Ty<'a> {
        let width = bundle_tys(arg_tys).map(|ty| ty.integer_size().bits()).sum::<u16>();
        c.ty(TyKind::Uint(IntSize(width)))
    }

    fn decompose(&self, c: &Circuit<'a>, args: &[Wire<'a>]) -> Wire<'a> {
        let width = bundle_wires(c, args).map(|w| w.ty.integer_size().bits()).sum::<u16>();
        let out_ty = c.ty(TyKind::Uint(IntSize(width)));
        let u16_ty = c.ty(TyKind::U16);
        let mut pos = 0;
        let mut acc = c.lit(out_ty, 0);
        for w in bundle_wires(c, args) {
            acc = c.or(acc, c.shl(c.cast(w, out_ty), c.lit(u16_ty, pos)));
            pos += w.ty.integer_size().bits();
        }
        assert!(pos == width);
        acc
    }
}

pub fn concat_bits<'a, T: Flatten<'a>>(bld: &Builder<'a>, x: TWire<'a, T>) -> Wire<'a> {
    let w = T::to_wire(bld, x);
    let gk = bld.circuit().intern_gadget_kind(ConcatBits);
    bld.circuit().gadget(gk, &[w])
}


/// The reverse of `ConcatBits`: split a large `Uint` into pieces, producing something of the
/// indicated type (usually a `Bundle`).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SplitBits<'a>(pub Ty<'a>);
impl_gadget_kind_support!(<'a> SplitBits<'a>);

impl<'a> GadgetKind<'a> for SplitBits<'a> {
    fn transfer<'b>(&self, c: &Circuit<'b>) -> GadgetKindRef<'b> {
        c.intern_gadget_kind(SplitBits(self.0.transfer(c)))
    }

    fn typecheck(&self, _c: &Circuit<'a>, arg_tys: &[Ty<'a>]) -> Ty<'a> {
        let width = bundle_tys(&[self.0]).map(|ty| ty.integer_size().bits()).sum::<u16>();
        assert!(arg_tys.len() == 1, "expected exactly 1 input for SplitBits");
        assert!(
            *arg_tys[0] == TyKind::Uint(IntSize(width)),
            "expected Uint({}), but got {:?}", width, arg_tys[0],
        );
        self.0
    }

    fn decompose(&self, c: &Circuit<'a>, args: &[Wire<'a>]) -> Wire<'a> {
        fn walk<'a>(c: &Circuit<'a>, inp: Wire<'a>, ty: Ty<'a>, pos: &mut u16) -> Wire<'a> {
            match *ty {
                TyKind::Uint(sz) => {
                    let (start, end) = (*pos, *pos + sz.bits());
                    *pos = end;
                    extract_bits(c, inp, start, end)
                },
                TyKind::Int(sz) => {
                    let (start, end) = (*pos, *pos + sz.bits());
                    *pos = end;
                    c.cast(extract_bits(c, inp, start, end), ty)
                },
                TyKind::Bundle(tys) => {
                    c.pack_iter(tys.iter().map(|&ty| walk(c, inp, ty, pos)))
                },
            }
        }
        let mut pos = 0;
        walk(c, args[0], self.0, &mut pos)
    }
}

pub fn split_bits<'a, T: Flatten<'a>>(bld: &Builder<'a>, w: Wire<'a>) -> TWire<'a, T> {
    let ty = T::wire_type(bld.circuit());
    let gk = bld.circuit().intern_gadget_kind(SplitBits(ty));
    T::from_wire(bld, bld.circuit().gadget(gk, &[w]))
}


/// Extract a range of bits from an unsigned integer.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct ExtractBits {
    pub start: u16,
    pub end: u16,
}
impl_gadget_kind_support!(ExtractBits);

impl<'a> GadgetKind<'a> for ExtractBits {
    fn transfer<'b>(&self, c: &Circuit<'b>) -> GadgetKindRef<'b> {
        c.intern_gadget_kind(self.clone())
    }

    fn typecheck(&self, c: &Circuit<'a>, arg_tys: &[Ty<'a>]) -> Ty<'a> {
        assert!(arg_tys.len() == 1, "expected exactly 1 input for ExtractBits");
        let arg_width = match *arg_tys[0] {
            TyKind::Uint(sz) => sz.bits(),
            ty => panic!("expected Uint, but got {:?}", ty),
        };
        assert!(
            self.start <= self.end && self.end <= arg_width,
            "can't extract {}..{} from u{}",
            self.start, self.end, arg_width,
        );
        c.ty(TyKind::Uint(IntSize(self.end - self.start)))
    }

    fn decompose(&self, c: &Circuit<'a>, args: &[Wire<'a>]) -> Wire<'a> {
        let u16_ty = c.ty(TyKind::U16);
        let out_ty = c.ty(TyKind::Uint(IntSize(self.end - self.start)));
        let shifted = c.shr(args[0], c.lit(u16_ty, self.start));
        c.cast(shifted, out_ty)
    }
}

pub fn extract_bits<'a>(c: &Circuit<'a>, w: Wire<'a>, start: u16, end: u16) -> Wire<'a> {
    let gk = c.intern_gadget_kind(ExtractBits { start, end });
    c.gadget(gk, &[w])
}

/// Extract enough low bits from `w` to construct a value of type `T`.
pub fn extract_low<'a, T: Flatten<'a>>(bld: &Builder<'a>, w: Wire<'a>) -> TWire<'a, T> {
    let c = bld.circuit();
    let ty = T::wire_type(c);
    let width = bundle_tys(&[ty]).map(|ty| ty.integer_size().bits()).sum::<u16>();
    let gk = c.intern_gadget_kind(ExtractBits { start: 0, end: width });
    let out_wire = c.gadget(gk, &[w]);
    T::from_wire(bld, out_wire)
}
