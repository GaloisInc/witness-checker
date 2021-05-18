use std::alloc::Layout;
use std::any;
use std::cell::{Cell, RefCell};
use std::collections::HashSet;
use std::convert::TryFrom;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::ops::{Deref, Range};
use std::slice;
use std::str;
use bumpalo::Bump;
use num_bigint::{BigUint, BigInt, Sign};
use overridable_trait::define_overridable_trait;


/// A high-level arithmetic/boolean circuit.
///
/// This circuit representation has no notion of a "public wire" - all wires carry secret values.
/// This works because we provide no "open" or "reveal" operation.  The only way to produce a
/// public/cleartext value is with `GateKind::Lit`, which contains a compile-time constant, so any
/// operations over literals can be computed entirely at compile time.
///
/// If a witness is available, the `Circuit` includes its values.  This allows circuit
/// transformations to make corresponding changes to the witness if necessary.  The full witness is
/// not represented explicitly, but the individual values are accessible through the
/// `GateKind::Secret` gates present in the circuit.  Use the `walk_witness` function to obtain the
/// witness values that are used to compute some set of `Wire`s.
pub struct Circuit<'a> {
    arena: &'a Bump,
    // TODO: clean up interning
    // Currently it's possible to get two distinct interned pointers for the same value (e.g.,
    // `ty1` and `ty2` where `ty1 != ty2` but `*ty1 == *ty2`) by creating two different `Circuit`s
    // backed by the same arena.  We should have a combined structure that owns both the arena and
    // the interning tables, though that might require a bit of unsafe code.
    intern_gate: RefCell<HashSet<&'a Gate<'a>>>,
    intern_ty: RefCell<HashSet<&'a TyKind<'a>>>,
    intern_wire_list: RefCell<HashSet<&'a [Wire<'a>]>>,
    intern_ty_list: RefCell<HashSet<&'a [Ty<'a>]>>,
    intern_gadget_kind: RefCell<HashSet<&'a HashDynGadgetKind<'a>>>,
    intern_str: RefCell<HashSet<&'a str>>,
    intern_bits: RefCell<HashSet<&'a [u32]>>,

    current_label: Cell<&'a str>,
    is_prover: bool,
}

impl<'a> Circuit<'a> {
    pub fn new(arena: &'a Bump, is_prover: bool) -> Circuit<'a> {
        Circuit {
            arena,
            intern_gate: RefCell::new(HashSet::new()),
            intern_ty: RefCell::new(HashSet::new()),
            intern_wire_list: RefCell::new(HashSet::new()),
            intern_ty_list: RefCell::new(HashSet::new()),
            intern_gadget_kind: RefCell::new(HashSet::new()),
            intern_str: RefCell::new(HashSet::new()),
            intern_bits: RefCell::new(HashSet::new()),
            current_label: Cell::new(""),
            is_prover,
        }
    }

    fn intern_gate(&self, gate: Gate<'a>) -> &'a Gate<'a> {
        let mut intern = self.intern_gate.borrow_mut();
        match intern.get(&gate) {
            Some(x) => x,
            None => {
                let gate = self.arena.alloc(gate);
                intern.insert(gate);
                gate
            },
        }
    }

    fn intern_ty(&self, ty: TyKind<'a>) -> &'a TyKind<'a> {
        let mut intern = self.intern_ty.borrow_mut();
        match intern.get(&ty) {
            Some(x) => x,
            None => {
                let ty = self.arena.alloc(ty);
                intern.insert(ty);
                ty
            },
        }
    }

    fn intern_wire_list(&self, wire_list: &[Wire<'a>]) -> &'a [Wire<'a>] {
        let mut intern = self.intern_wire_list.borrow_mut();
        match intern.get(wire_list) {
            Some(&x) => x,
            None => {
                let wire_list = self.arena.alloc_slice_copy(wire_list);
                intern.insert(wire_list);
                wire_list
            },
        }
    }

    fn intern_ty_list(&self, ty_list: &[Ty<'a>]) -> &'a [Ty<'a>] {
        let mut intern = self.intern_ty_list.borrow_mut();
        match intern.get(ty_list) {
            Some(&x) => x,
            None => {
                let ty_list = self.arena.alloc_slice_copy(ty_list);
                intern.insert(ty_list);
                ty_list
            },
        }
    }

    fn intern_str(&self, s: &str) -> &'a str {
        let mut intern = self.intern_str.borrow_mut();
        match intern.get(s) {
            Some(&x) => x,
            None => {
                let s_bytes = self.arena.alloc_slice_copy(s.as_bytes());
                let s = unsafe { str::from_utf8_unchecked(s_bytes) };
                intern.insert(s);
                s
            },
        }
    }
}

define_overridable_trait! {
    lifetime 'a;
    trait CircuitTrait;
    struct Circuit;
    dyn DynCircuit;

    // TODO: temporary function - remove once refactoring is done
    pub fn as_base(&self) -> &Circuit<'a> {
        self
    }

    pub fn is_prover(&self) -> bool {
        self.is_prover
    }

    pub fn intern_bits(&self, b: &[u32]) -> Bits<'a> {
        let mut intern = self.intern_bits.borrow_mut();
        match intern.get(b) {
            Some(&x) => Bits(x),
            None => {
                let b = self.arena.alloc_slice_copy(b);
                intern.insert(b);
                Bits(b)
            },
        }
    }

    /// Intern a gadget kind so it can be used to construct `Gadget` gates.  It's legal to intern
    /// the same `GadgetKind` more than once, so this can be used inside stateless lowering passes
    /// (among other things).
    pub fn intern_gadget_kind<G: GadgetKind<'a>>(&self, g: G) -> GadgetKindRef<'a> {
        let mut intern = self.intern_gadget_kind.borrow_mut();
        match intern.get(HashDynGadgetKind::new(&g)) {
            Some(&x) => {
                GadgetKindRef(&x.0)
            },
            None => {
                let g = self.arena.alloc(g);
                intern.insert(HashDynGadgetKind::new(g));
                GadgetKindRef(g)
            },
        }
    }

    pub fn intern_gadget_kind_dyn(&self, g: &dyn GadgetKind<'a>) -> GadgetKindRef<'a> {
        let mut intern = self.intern_gadget_kind.borrow_mut();
        match intern.get(HashDynGadgetKind::new(g)) {
            Some(&x) => {
                GadgetKindRef(&x.0)
            },
            None => {
                let g = unsafe {
                    // Clone `g` into the arena.  This is tricky since we don't know its concrete
                    // type.
                    let layout = Layout::from_size_align(
                        mem::size_of_val(g),
                        mem::align_of_val(g),
                    ).unwrap();
                    let dest = self.arena.alloc_layout(layout);
                    g.clone_dyn(dest.as_ptr());
                    &*g.make_dyn(dest.as_ptr())
                };
                intern.insert(HashDynGadgetKind::new(g));
                GadgetKindRef(g)
            },
        }
    }

    pub fn gate(&self, kind: GateKind<'a>) -> Wire<'a> {
        // Forbid constructing gates that violate type-safety invariants.
        match kind {
            GateKind::Binary(op, a, b) => {
                assert!(
                    a.ty == b.ty,
                    "type mismatch for {:?}: {:?} != {:?}", op, a.ty, b.ty,
                );
            },
            GateKind::Shift(op, _, b) => match *b.ty {
                TyKind::Uint(_) => {},
                _ => panic!("{:?} shift amount must be a Uint, not {:?}", op, b.ty),
            },
            GateKind::Compare(op, a, b) => {
                assert!(
                    a.ty == b.ty,
                    "type mismatch for {:?}: {:?} != {:?}", op, a.ty, b.ty,
                );
            },
            GateKind::Mux(c, t, e) => {
                assert!(
                    *c.ty == TyKind::BOOL,
                    "mux condition must be {:?}, not {:?}", TyKind::BOOL, c.ty,
                );
                assert!(
                    t.ty == e.ty,
                    "type mismatch for mux: {:?} != {:?}", c.ty, e.ty,
                );
            },
            GateKind::Extract(w, i) => match *w.ty {
                TyKind::Bundle(tys) => {
                    if i >= tys.len() {
                        panic!(
                            "index out of range for extract: {} >= {} ({:?})",
                            i, tys.len(), tys,
                        );
                    }
                },
                _ => panic!("bad input type for extract: {:?} (expected Bundle)", w.ty),
            },
            // GateKind::Gadget typechecking happens in the call to `kind.ty`
            _ => {},
        }

        Wire(self.intern_gate(Gate {
            ty: kind.ty(self),
            kind,
            label: self.current_label.get(),
        }))
    }

    pub fn ty(&self, kind: TyKind<'a>) -> Ty<'a> {
        Ty(self.intern_ty(kind))
    }

    pub fn ty_bundle(&self, tys: &[Ty<'a>]) -> Ty<'a> {
        self.ty(TyKind::Bundle(self.intern_ty_list(tys)))
    }

    pub fn ty_bundle_iter<I>(&self, it: I) -> Ty<'a>
    where I: IntoIterator<Item = Ty<'a>> {
        let tys = it.into_iter().collect::<Vec<_>>();
        self.ty_bundle(&tys)
    }

    pub fn lit<T: AsBits>(&self, ty: Ty<'a>, val: T) -> Wire<'a> {
        let val = self.bits(ty, val);
        self.gate(GateKind::Lit(val, ty))
    }

    pub fn lit_dyn(&self, ty: Ty<'a>, val: AnyAsBits) -> Wire<'a> {
        let val = self.bits_dyn(ty, val);
        self.gate(GateKind::Lit(val, ty))
    }

    pub fn secret(&self, secret: Secret<'a>) -> Wire<'a> {
        self.gate(GateKind::Secret(secret))
    }

    /// Add a new secret value to the witness, and return a `Wire` that carries that value.  The
    /// accompanying `SecretHandle` can be used to assign a value to the secret after construction.
    /// If the `SecretHandle` is dropped without setting a value, the value will be set to zero
    /// automatically.
    pub fn new_secret(&self, ty: Ty<'a>) -> (Wire<'a>, SecretHandle<'a>) {
        let default = self.intern_bits(&[]);
        self.new_secret_default(ty, default)
    }

    /// Like `new_secret`, but dropping the `SecretHandle` without setting a value will set the
    /// value to `default` instead of zero.
    pub fn new_secret_default<T: AsBits>(
        &self,
        ty: Ty<'a>,
        default: T,
    ) -> (Wire<'a>, SecretHandle<'a>) {
        let val = if self.is_prover { Some(SecretValue::default()) } else { None };
        let default = self.bits(ty, default);
        let secret = Secret(self.arena.alloc(SecretData { ty, val }));
        let handle = SecretHandle::new(secret, default);
        (self.secret(secret), handle)
    }

    /// Add a new secret value to the witness, initialize it with the result of `mk_val()` (if
    /// running in prover mode), and return a `Wire` that carries that value.
    ///
    /// `mk_val` will not be called when running in prover mode.
    pub fn new_secret_init<T: AsBits, F>(&self, ty: Ty<'a>, mk_val: F) -> Wire<'a>
    where F: FnOnce() -> T {
        let val = if self.is_prover {
            let bits = self.bits(ty, mk_val());
            Some(SecretValue::with_value(bits))
        } else {
            None
        };
        let secret = Secret(self.arena.alloc(SecretData { ty, val }));
        self.secret(secret)
    }

    /// Create a new uninitialized secret.  When running in prover mode, the secret must be
    /// initialized later using `SecretData::set_from_lit`.
    pub fn new_secret_uninit(&self, ty: Ty<'a>) -> Wire<'a> {
        let val = if self.is_prover { Some(SecretValue::default()) } else { None };
        let secret = Secret(self.arena.alloc(SecretData { ty, val }));
        self.secret(secret)
    }

    pub fn bits<T: AsBits>(&self, ty: Ty<'a>, val: T) -> Bits<'a> {
        let sz = match *ty {
            TyKind::Int(sz) | TyKind::Uint(sz) => sz,
            _ => panic!("can't construct bit representation for non-integer type {:?}", ty),
        };
        let val = val.as_bits(self, sz);
        assert!(val.width() <= sz.bits());
        val
    }

    pub fn bits_dyn(&self, ty: Ty<'a>, val: AnyAsBits) -> Bits<'a> {
        self.bits(ty, val)
    }


    pub fn unary(&self, op: UnOp, arg: Wire<'a>) -> Wire<'a> {
        self.gate(GateKind::Unary(op, arg))
    }

    pub fn neg(&self, arg: Wire<'a>) -> Wire<'a> {
        self.unary(UnOp::Neg, arg)
    }

    pub fn not(&self, arg: Wire<'a>) -> Wire<'a> {
        self.unary(UnOp::Not, arg)
    }

    pub fn binary(&self, op: BinOp, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.gate(GateKind::Binary(op, a, b))
    }

    pub fn add(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::Add, a, b)
    }

    pub fn sub(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::Sub, a, b)
    }

    pub fn mul(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::Mul, a, b)
    }

    pub fn div(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::Div, a, b)
    }

    pub fn mod_(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::Mod, a, b)
    }

    pub fn and(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::And, a, b)
    }

    pub fn or(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::Or, a, b)
    }

    pub fn all_true<I: Iterator<Item=Wire<'a>>>(&self, wires: I) -> Wire<'a> {
        let true_if_empty = self.lit(self.ty(TyKind::BOOL), 1);
        wires.fold(
            true_if_empty,
            |all_true, w| self.and(all_true, w),
        )
    }

    pub fn any_true<I: Iterator<Item=Wire<'a>>>(&self, wires: I) -> Wire<'a> {
        let false_if_empty = self.lit(self.ty(TyKind::BOOL), 0);
        wires.fold(
            false_if_empty,
            |any_true, w| self.or(any_true, w),
        )
    }

    pub fn xor(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::Xor, a, b)
    }

    pub fn shift(&self, op: ShiftOp, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.gate(GateKind::Shift(op, a, b))
    }

    pub fn shl(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.shift(ShiftOp::Shl, a, b)
    }

    pub fn shr(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.shift(ShiftOp::Shr, a, b)
    }

    pub fn compare(&self, op: CmpOp, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.gate(GateKind::Compare(op, a, b))
    }

    pub fn eq(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.compare(CmpOp::Eq, a, b)
    }

    pub fn ne(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.compare(CmpOp::Ne, a, b)
    }

    pub fn lt(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.compare(CmpOp::Lt, a, b)
    }

    pub fn le(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.compare(CmpOp::Le, a, b)
    }

    pub fn gt(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.compare(CmpOp::Gt, a, b)
    }

    pub fn ge(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.compare(CmpOp::Ge, a, b)
    }

    pub fn mux(&self, c: Wire<'a>, t: Wire<'a>, e: Wire<'a>) -> Wire<'a> {
        self.gate(GateKind::Mux(c, t, e))
    }

    pub fn cast(&self, w: Wire<'a>, ty: Ty<'a>) -> Wire<'a> {
        self.gate(GateKind::Cast(w, ty))
    }

    pub fn pack(&self, ws: &[Wire<'a>]) -> Wire<'a> {
        let ws = self.intern_wire_list(ws);
        self.gate(GateKind::Pack(ws))
    }

    pub fn pack_iter<I>(&self, it: I) -> Wire<'a>
    where I: IntoIterator<Item = Wire<'a>> {
        let ws = it.into_iter().collect::<Vec<_>>();
        self.pack(&ws)
    }

    pub fn extract(&self, w: Wire<'a>, i: usize) -> Wire<'a> {
        self.gate(GateKind::Extract(w, i))
    }

    pub fn gadget(&self, kind: GadgetKindRef<'a>, args: &[Wire<'a>]) -> Wire<'a> {
        let args = self.intern_wire_list(args);
        self.gate(GateKind::Gadget(kind, args))
    }

    pub fn gadget_iter<I>(&self, kind: GadgetKindRef<'a>, it: I) -> Wire<'a>
    where I: IntoIterator<Item = Wire<'a>> {
        let args = it.into_iter().collect::<Vec<_>>();
        self.gadget(kind, &args)
    }


    pub fn scoped_label<T: fmt::Display>(&self, label: T) -> CellResetGuard<&'a str> {
        let old = self.current_label();
        self.scoped_label_exact(format_args!("{}/{}", old, label))
    }

    pub fn with_label<T: fmt::Display, F: FnOnce() -> R, R>(&self, label: T, f: F) -> R {
        let _g = self.scoped_label(label);
        f()
    }

    pub fn scoped_label_exact<T: fmt::Display>(&self, label: T) -> CellResetGuard<&'a str> {
        let new = self.intern_str(&label.to_string());
        CellResetGuard::new(&self.current_label, new)
    }

    pub fn scoped_label_exact_dyn(&self, label: &str) -> CellResetGuard<&'a str> {
        let new = self.intern_str(label);
        CellResetGuard::new(&self.current_label, new)
    }

    pub fn current_label(&self) -> &'a str {
        self.current_label.get()
    }
}

impl<'a, 'b> CircuitTrait<'a> for &'b DynCircuit<'a> {
    type Inner = DynCircuit<'a>;
    fn inner(&self) -> &DynCircuit<'a> { &**self }
}


impl<'a> DynCircuit<'a> {
    pub fn intern_gadget_kind<G: GadgetKind<'a>>(&self, g: G) -> GadgetKindRef<'a> {
        self.intern_gadget_kind_dyn(&g)
    }

    pub fn lit<T: AsBits>(&self, ty: Ty<'a>, val: T) -> Wire<'a> {
        self.lit_dyn(ty, val.as_any())
    }

    pub fn scoped_label<T: fmt::Display>(&self, label: T) -> CellResetGuard<&'a str> {
        let old = self.current_label();
        self.scoped_label_exact_dyn(&format!("{}/{}", old, label))
    }

    pub fn with_label<T: fmt::Display, F: FnOnce() -> R, R>(&self, label: T, f: F) -> R {
        let _g = self.scoped_label(label);
        f()
    }

    pub fn scoped_label_exact<T: fmt::Display>(&self, label: T) -> CellResetGuard<&'a str> {
        self.scoped_label_exact_dyn(&label.to_string())
    }
}


pub struct WireDeps<'a> {
    inner: WireDepsInner<'a>,
}

enum WireDepsInner<'a> {
    Small(Range<u8>, [Option<Wire<'a>>; 3]),
    Large(slice::Iter<'a, Wire<'a>>),
}

impl<'a> WireDeps<'a> {
    fn zero() -> WireDeps<'a> {
        Self::small(0, [None, None, None])
    }

    fn one(a: Wire<'a>) -> WireDeps<'a> {
        Self::small(1, [Some(a), None, None])
    }

    fn two(a: Wire<'a>, b: Wire<'a>) -> WireDeps<'a> {
        Self::small(2, [Some(a), Some(b), None])
    }

    fn three(a: Wire<'a>, b: Wire<'a>, c: Wire<'a>) -> WireDeps<'a> {
        Self::small(3, [Some(a), Some(b), Some(c)])
    }

    fn small(n: u8, arr: [Option<Wire<'a>>; 3]) -> WireDeps<'a> {
        WireDeps {
            inner: WireDepsInner::Small(0..n, arr),
        }
    }

    fn many(ws: &'a [Wire<'a>]) -> WireDeps<'a> {
        WireDeps {
            inner: WireDepsInner::Large(ws.iter()),
        }
    }
}

impl<'a> Iterator for WireDepsInner<'a> {
    type Item = Wire<'a>;
    fn next(&mut self) -> Option<Wire<'a>> {
        match *self {
            WireDepsInner::Small(ref mut range, ref arr) => {
                let i = range.next()? as usize;
                arr.get(i).and_then(|&x| x)
            },
            WireDepsInner::Large(ref mut it) => it.next().cloned(),
        }
    }
}

impl<'a> DoubleEndedIterator for WireDepsInner<'a> {
    fn next_back(&mut self) -> Option<Wire<'a>> {
        match *self {
            WireDepsInner::Small(ref mut range, ref arr) => {
                let i = range.next_back()? as usize;
                arr.get(i).and_then(|&x| x)
            },
            WireDepsInner::Large(ref mut it) => it.next_back().cloned(),
        }
    }
}

impl<'a> Iterator for WireDeps<'a> {
    type Item = Wire<'a>;
    fn next(&mut self) -> Option<Wire<'a>> {
        self.inner.next()
    }
}

impl<'a> DoubleEndedIterator for WireDeps<'a> {
    fn next_back(&mut self) -> Option<Wire<'a>> {
        self.inner.next_back()
    }
}

pub fn wire_deps<'a>(w: Wire<'a>) -> WireDeps<'a> {
    match w.kind {
        GateKind::Lit(_, _) |
        GateKind::Secret(_) => WireDeps::zero(),
        GateKind::Unary(_, a) |
        GateKind::Cast(a, _) |
        GateKind::Extract(a, _) => WireDeps::one(a),
        GateKind::Binary(_, a, b) |
        GateKind::Shift(_, a, b) |
        GateKind::Compare(_, a, b) => WireDeps::two(a, b),
        GateKind::Mux(c, t, e) => WireDeps::three(c, t, e),
        GateKind::Pack(ws) |
        GateKind::Gadget(_, ws) => WireDeps::many(ws),
    }
}

pub struct PostorderIter<'a, F> {
    stack: Vec<Wire<'a>>,
    /// Wires that have already been yielded.  We avoid processing the same wire twice.
    seen: HashSet<Wire<'a>>,
    filter: F,
}

impl<'a, F: FnMut(Wire<'a>) -> bool> Iterator for PostorderIter<'a, F> {
    type Item = Wire<'a>;
    fn next(&mut self) -> Option<Wire<'a>> {
        // NB: `last().cloned()`, not `pop()`.  We only pop the item if all its children have been
        // processed.
        while let Some(wire) = self.stack.last().cloned() {
            // We may end up with the same wire on the stack twice, if the wire is accessible via
            // two different paths.
            if self.seen.contains(&wire) {
                self.stack.pop();
                continue;
            }

            let maybe_push = |w| {
                if self.seen.contains(&w) || !(self.filter)(w) {
                    false
                } else {
                    self.stack.push(w);
                    true
                }
            };

            let children_pending = wire_deps(wire).rev().any(maybe_push);

            if !children_pending {
                let result = self.stack.pop();
                debug_assert!(result == Some(wire));
                self.seen.insert(wire);
                return Some(wire);
            }
        }
        None
    }
}

pub fn walk_wires<'a, I>(wires: I) -> impl Iterator<Item = Wire<'a>>
where I: IntoIterator<Item = Wire<'a>> {
    let mut stack = wires.into_iter().collect::<Vec<_>>();
    stack.reverse();
    PostorderIter {
        stack,
        seen: HashSet::new(),
        filter: |_| true,
    }
}

pub fn walk_wires_filtered<'a, I, F>(wires: I, filter: F) -> PostorderIter<'a, F>
where I: IntoIterator<Item = Wire<'a>>, F: FnMut(Wire<'a>) -> bool {
    let mut stack = wires.into_iter().collect::<Vec<_>>();
    stack.reverse();
    PostorderIter {
        stack,
        seen: HashSet::new(),
        filter,
    }
}

/// Visit all `Secret`s that are used in the computation of `wires`.  Yields each `Secret`
/// once, in some deterministic order (assuming `wires` itself is deterministic).
pub fn walk_witness<'a, I>(wires: I) -> impl Iterator<Item = Secret<'a>>
where I: IntoIterator<Item = Wire<'a>> {
    walk_wires(wires).filter_map(|w| match w.kind {
        GateKind::Secret(s) => Some(s),
        _ => None,
    })
}


#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct IntSize(pub u16);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum TyKind<'a> {
    Int(IntSize),
    Uint(IntSize),
    Bundle(&'a [Ty<'a>]),
}

impl IntSize {
    pub fn bits(self) -> u16 {
        self.0
    }
}

impl TyKind<'_> {
    pub const I8: TyKind<'static> = TyKind::Int(IntSize(8));
    pub const I16: TyKind<'static> = TyKind::Int(IntSize(16));
    pub const I32: TyKind<'static> = TyKind::Int(IntSize(32));
    pub const I64: TyKind<'static> = TyKind::Int(IntSize(64));
    pub const U8: TyKind<'static> = TyKind::Uint(IntSize(8));
    pub const U16: TyKind<'static> = TyKind::Uint(IntSize(16));
    pub const U32: TyKind<'static> = TyKind::Uint(IntSize(32));
    pub const U64: TyKind<'static> = TyKind::Uint(IntSize(64));
    pub const BOOL: TyKind<'static> = TyKind::Uint(IntSize(1));

    pub fn is_integer(&self) -> bool {
        match *self {
            TyKind::Int(_) => true,
            TyKind::Uint(_) => true,
            TyKind::Bundle(_) => false,
        }
    }

    pub fn integer_size(&self) -> IntSize {
        match *self {
            TyKind::Int(sz) => sz,
            TyKind::Uint(sz) => sz,
            TyKind::Bundle(_) => panic!("Bundle has no IntSize"),
        }
    }

    pub fn is_int(&self) -> bool {
        match *self {
            TyKind::Int(_) => true,
            _ => false,
        }
    }

    pub fn is_uint(&self) -> bool {
        match *self {
            TyKind::Uint(_) => true,
            _ => false,
        }
    }

    pub fn transfer<'b>(&self, c: &Circuit<'b>) -> Ty<'b> {
        match *self {
            TyKind::Uint(sz) => CircuitTrait::ty(c, TyKind::Uint(sz)),
            TyKind::Int(sz) => CircuitTrait::ty(c, TyKind::Int(sz)),
            TyKind::Bundle(tys) => {
                c.ty_bundle_iter(tys.iter().map(|ty| ty.transfer(c)))
            },
        }
    }
}


#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Gate<'a> {
    /// Cached output type of this gate.  Computed when the `Gate` is created.  The result is
    /// stored here so that `GateKind::ty` runs in constant time, rather than potentially having
    /// recurse over the entire depth of the circuit.
    pub ty: Ty<'a>,
    pub kind: GateKind<'a>,
    pub label: &'a str,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum GateKind<'a> {
    /// A literal/constant value.
    Lit(Bits<'a>, Ty<'a>),
    /// Retrieve a secret value from the witness.
    Secret(Secret<'a>),
    /// Compute a unary operation.  All `UnOp`s have type `T -> T`.
    Unary(UnOp, Wire<'a>),
    /// Compute a binary operation.  All `BinOp`s have type `T -> T -> T`
    Binary(BinOp, Wire<'a>, Wire<'a>),
    /// Compute a binary operation.  All `BinOp`s have type `T -> u8 -> T`
    Shift(ShiftOp, Wire<'a>, Wire<'a>),
    /// Compute a comparison operation.  All `CmpOp`s have type `T -> T -> bool`.
    Compare(CmpOp, Wire<'a>, Wire<'a>),
    /// `Mux(cond, then_, else)`: depending on `cond`, select either `then_` or `else`.
    Mux(Wire<'a>, Wire<'a>, Wire<'a>),
    /// Convert a value to a different type.
    Cast(Wire<'a>, Ty<'a>),
    /// Pack several values into a bundle.
    Pack(&'a [Wire<'a>]),
    /// Extract one value from a bundle.
    Extract(Wire<'a>, usize),
    /// A custom gadget.
    // TODO: move fields to a struct (this variant is 5 words long)
    Gadget(GadgetKindRef<'a>, &'a [Wire<'a>]),
}

impl<'a> GateKind<'a> {
    pub fn ty(&self, c: &Circuit<'a>) -> Ty<'a> {
        match *self {
            GateKind::Lit(_, ty) => ty,
            GateKind::Secret(s) => s.ty,
            GateKind::Unary(_, w) => w.ty,
            GateKind::Binary(_, w, _) => w.ty,
            GateKind::Shift(_, w, _) => w.ty,
            GateKind::Compare(_, _, _) => CircuitTrait::ty(c, TyKind::BOOL),
            GateKind::Mux(_, w, _) => w.ty,
            GateKind::Cast(_, ty) => ty,
            GateKind::Pack(ws) => c.ty_bundle_iter(ws.iter().map(|&w| w.ty)),
            GateKind::Extract(w, i) => match *w.ty {
                TyKind::Bundle(tys) => tys[i],
                _ => panic!("invalid wire type {:?} in Extract", w.ty),
            },
            GateKind::Gadget(k, ws) => {
                let tys = ws.iter().map(|w| w.ty).collect::<Vec<_>>();
                k.typecheck(c, &tys)
            },
        }
    }

    pub fn as_secret(&self) -> Secret<'a> {
        match *self {
            GateKind::Secret(s) => s,
            _ => panic!("expected GateKind::Secret"),
        }
    }

    pub fn as_lit(&self) -> (Ty<'a>, Bits<'a>) {
        match *self {
            GateKind::Lit(b, t) => (t, b),
            _ => panic!("expected GateKind::Lit"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum BinOp {
    Add, Sub, Mul, Div, Mod,
    And, Or, Xor,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum ShiftOp {
    Shl, Shr,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum CmpOp {
    Eq, Ne, Lt, Le, Gt, Ge,
}


/// Declare a wrapper around an immutable reference, with `Eq` and `Hash` instances that compare by
/// address instead of by value.
macro_rules! declare_interned_pointer {
    ($(#[$attr:meta])* $pub_:vis struct $Ptr:ident <$lt:lifetime> => $T:ty;) => {
        $(#[$attr])*
        #[derive(Clone, Copy)]
        $pub_ struct $Ptr<$lt>(&$lt $T);

        impl<$lt> $Ptr<$lt> {
            pub fn as_ptr(self) -> *const $T {
                self.0 as *const $T
            }
        }

        impl<$lt> PartialEq for $Ptr<$lt> {
            fn eq(&self, other: &$Ptr<$lt>) -> bool {
                self.0 as *const _ == other.0 as *const _
            }

            fn ne(&self, other: &$Ptr<$lt>) -> bool {
                self.0 as *const _ != other.0 as *const _
            }
        }

        impl Eq for $Ptr<'_> {}

        impl<$lt> Hash for $Ptr<$lt> {
            fn hash<H: Hasher>(&self, state: &mut H) {
                (self.0 as *const $T).hash(state)
            }
        }

        impl<$lt> Deref for $Ptr<$lt> {
            type Target = $T;
            fn deref(&self) -> &$T {
                self.0
            }
        }

        impl<$lt> fmt::Pointer for $Ptr<$lt> {
            fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
                fmt::Pointer::fmt(&self.as_ptr(), fmt)
            }
        }
    };
}

declare_interned_pointer! {
    /// The output of a `Gate`, which carries a value during circuit evaluation.
    pub struct Wire<'a> => Gate<'a>;
}

thread_local! {
    static WIRE_DEBUG_DEPTH: Cell<usize> = Cell::new(2);
}

impl<'a> fmt::Debug for Wire<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        WIRE_DEBUG_DEPTH.with(|depth_cell| {
            let depth = depth_cell.get();
            if depth > 0 {
                depth_cell.set(depth - 1);
                let r = write!(fmt, "Wire({:p} => {:?})", self.0, self.0);
                depth_cell.set(depth);
                r
            } else {
                write!(fmt, "Wire({:p})", self.0)
            }
        })
    }
}

declare_interned_pointer! {
    /// A secret input value, part of the witness.
    #[derive(Debug)]
    pub struct Secret<'a> => SecretData<'a>;
}

#[derive(Clone, PartialEq, Eq, Debug, Default)]
struct SecretValue<'a>(Cell<Option<Bits<'a>>>);

impl<'a> SecretValue<'a> {
    pub fn with_value(val: Bits<'a>) -> SecretValue<'a> {
        SecretValue(Cell::new(Some(val)))
    }

    pub fn set(&self, val: Bits<'a>) {
        assert!(self.0.get().is_none(), "secret value has already been set");
        self.0.set(Some(val));
    }

    pub fn set_default(&self, val: Bits<'a>) {
        if self.0.get().is_none() {
            self.0.set(Some(val));
        }
    }

    pub fn get(&self) -> Bits<'a> {
        match self.0.get() {
            Some(x) => x,
            None => panic!("tried to access uninitialized secret value"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SecretData<'a> {
    pub ty: Ty<'a>,
    val: Option<SecretValue<'a>>,
}

impl<'a> SecretData<'a> {
    /// Retrieve the value of this secret.  Returns `None` in verifier mode, or `Some(bits)` in
    /// prover mode.  In prover mode, if the value has not been initialized yet, this function will
    /// panic.
    pub fn val(&self) -> Option<Bits<'a>> {
        self.val.as_ref().map(|sv| sv.get())
    }

    pub fn set(&self, bits: Bits<'a>) {
        let sv = self.val.as_ref()
            .expect("can't provide secret values when running in verifier mode");
        sv.set(bits);
    }

    pub fn set_default(&self, bits: Bits<'a>) {
        if let Some(ref sv) = self.val {
            sv.set_default(bits);
        }
    }

    pub fn set_from_lit(&self, w: Wire<'a>, force: bool) {
        let (ty, bits) = w.kind.as_lit();
        assert!(ty == self.ty, "type mismatch in secret init: {:?} != {:?}", ty, self.ty);
        if force {
            self.set(bits);
        } else {
            self.set_default(bits);
        }
    }
}

/// A handle that can be used to set the value of a `Secret`.  Sets a default value on drop, if a
/// default was provided when the handle was constructed.
#[derive(Debug)]
pub struct SecretHandle<'a> {
    s: Secret<'a>,
    default: Bits<'a>,
}

impl<'a> SecretHandle<'a> {
    fn new(s: Secret<'a>, default: Bits<'a>) -> SecretHandle<'a> {
        SecretHandle { s, default }
    }

    pub fn set(&self, c: &Circuit<'a>, val: impl AsBits) {
        let bits = c.bits(self.s.ty, val);
        self.s.set(bits);
    }
}

impl<'a> Drop for SecretHandle<'a> {
    fn drop(&mut self) {
        self.s.set_default(self.default);
    }
}



declare_interned_pointer! {
    #[derive(Debug)]
    pub struct Ty<'a> => TyKind<'a>;
}


pub unsafe trait GadgetKindSupport<'a> {
    fn type_name(&self) -> &'static str;
    fn eq_dyn(&self, other: &dyn GadgetKind<'a>) -> bool;
    fn hash_dyn(&self, state: &mut dyn Hasher);
    /// Clone `self` into `*dest`.  `dest` must be properly aligned.
    unsafe fn clone_dyn(&self, dest: *mut u8);
    /// Create a new `&dyn GadgetKindSupport` with the same type as `self` but a different data
    /// pointer.
    unsafe fn make_dyn(&self, data: *const u8) -> *const dyn GadgetKind<'a>;
}

macro_rules! impl_gadget_kind_support {
    (<$lt:lifetime> $T:ty) => {
        unsafe impl<$lt> $crate::ir::circuit::GadgetKindSupport<$lt> for $T {
            fn type_name(&self) -> &'static str { std::any::type_name::<$T>() }

            fn eq_dyn(&self, other: &dyn $crate::ir::circuit::GadgetKind<'a>) -> bool {
                unsafe {
                    let other = match $crate::ir::circuit::downcast_gadget_kind(other) {
                        Some(x) => x,
                        None => return false,
                    };
                    self == other
                }
            }

            fn hash_dyn(&self, mut state: &mut dyn core::hash::Hasher) {
                // Hash the type name first.  Otherwise all empty structs would have the same hash.
                core::hash::Hash::hash(self.type_name(), &mut state);
                core::hash::Hash::hash(self, &mut state);
            }

            unsafe fn clone_dyn(&self, dest: *mut u8) {
                (dest as *mut Self).write(core::clone::Clone::clone(self))
            }

            unsafe fn make_dyn(&self, data: *const u8) -> *const dyn GadgetKind<'a> {
                &*(data as *const Self)
            }
        }
    };

    ($T:ty) => { impl_gadget_kind_support! { <'a> $T } }
}

/// Defines a kind of gadget.  Instances of a gadget can be added to a `Circuit` using
/// `define_gadget_kind` and the `Circuit::gadget` constructor.
pub trait GadgetKind<'a>: GadgetKindSupport<'a> + 'a {
    /// Intern this `GadgetKind` into a new `Circuit`.  This should usually be implemented as
    ///
    /// ```Rust,ignore
    /// fn transfer<'b>(&self, c: &Circuit<'b>) -> GadgetKindRef<'b> {
    ///     c.intern_gadget_kind(self.clone())
    /// }
    /// ```
    ///
    /// However, this can't be provided automatically because it requires `Self: Clone + 'static`.
    /// The `Clone` bound implies `Sized`, which would make this trait non-object-safe, and
    /// `'static` means the `GadgetKind` can't contain any `Ty<'a>` values.
    fn transfer<'b>(&self, c: &Circuit<'b>) -> GadgetKindRef<'b>;

    /// Validate the argument types for an instance of this kind of gadget.  Returns the output
    /// type of a gadget.
    fn typecheck(&self, c: &Circuit<'a>, arg_tys: &[Ty<'a>]) -> Ty<'a>;

    /// Decompose this gadget into primitive gates.  This may be called if the backend doesn't
    /// support this gadget.
    fn decompose(&self, c: &Circuit<'a>, args: &[Wire<'a>]) -> Wire<'a>;
}

declare_interned_pointer! {
    pub struct GadgetKindRef<'a> => dyn GadgetKind<'a>;
}

impl<'a> GadgetKindRef<'a> {
    pub fn name(self) -> &'static str {
        self.type_name().split("::").last().unwrap_or("")
    }

    // TODO: there's probably some way to break memory safety with this, exploiting
    // co/contravariance of lifetimes
    pub fn cast<T: GadgetKind<'a>>(self) -> Option<&'a T> {
        unsafe { downcast_gadget_kind(self.0) }
    }
}

impl<'a> fmt::Debug for GadgetKindRef<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "GadgetKindRef({})", self.name())
    }
}

pub unsafe fn downcast_gadget_kind<'a, 'b, T: GadgetKind<'a>>(
    gk: &'b dyn GadgetKind<'a>,
) -> Option<&'b T> {
    if gk.type_name() != any::type_name::<T>() {
        None
    } else {
        Some(mem::transmute(gk as *const _ as *const u8))
    }
}


/// Helper type for making `dyn GadgetKind` hashable, so it can be stored in the `Circuit`'s
/// interning tables.
#[repr(transparent)]
struct HashDynGadgetKind<'a>(dyn GadgetKind<'a>);

impl<'a> HashDynGadgetKind<'a> {
    pub fn new<'b>(gk: &'b dyn GadgetKind<'a>) -> &'b HashDynGadgetKind<'a> {
        unsafe { mem::transmute(gk) }
    }
}

impl PartialEq for HashDynGadgetKind<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq_dyn(&other.0)
    }
}

impl Eq for HashDynGadgetKind<'_> {}

impl Hash for HashDynGadgetKind<'_> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.0.hash_dyn(h)
    }
}


pub struct CellResetGuard<'a, T> {
    cell: &'a Cell<T>,
    old: Cell<T>,
}

impl<'a, T> CellResetGuard<'a, T> {
    /// Set the contents of `cell` to `new`, and return a guard that restores the previous value
    /// when dropped.
    pub fn new(cell: &'a Cell<T>, new: T) -> CellResetGuard<'a, T> {
        let old = Cell::new(new);
        // We use `swap` to avoid copying the new or old value.
        cell.swap(&old);
        CellResetGuard { cell, old }
    }
}

impl<'a, T> Drop for CellResetGuard<'a, T> {
    fn drop(&mut self) {
        self.cell.swap(&self.old)
    }
}


/// An arbitrary-sized array of bits.  Used to represent integer values in the circuit and
/// evaluator.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Bits<'a>(pub &'a [u32]);

impl<'a> Bits<'a> {
    pub fn width(&self) -> u16 {
        for (i, &x) in self.0.iter().enumerate().rev() {
            if x != 0 {
                let b = (i + 1) * 32 - x.leading_zeros() as usize;
                return u16::try_from(b).unwrap();
            }
        }
        0
    }

    pub fn as_u64(&self) -> Option<u64> {
        match self.0.len() {
            0 => Some(0),
            1 => Some(self.0[0] as u64),
            2 => Some(self.0[0] as u64 | (self.0[1] as u64) << 32),
            _ => None,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.0.iter().all(|&x| x == 0)
    }

    pub fn to_biguint(&self) -> BigUint {
        BigUint::from_slice(self.0)
    }

    /// Interpret these bits as an integer of type `ty`.  For `TyKind::Uint(sz)`, the result is in
    /// the range `0 .. 2^sz`; for `TyKind::Int(sz)`, it's in the range `-2^(sz-1) .. 2^(sz-1)`.
    pub fn to_bigint(&self, ty: Ty) -> BigInt {
        match *ty {
            TyKind::Uint(sz) => {
                assert!(self.width() <= sz.bits());
                BigInt::from_biguint(Sign::Plus, BigUint::from_slice(self.0))
            },
            TyKind::Int(sz) => {
                assert!(self.width() <= sz.bits());
                let mut i = BigInt::from_biguint(Sign::Plus, BigUint::from_slice(self.0));
                let sign_bit = sz.bits() as usize - 1;
                let sb_idx = sign_bit / 32;
                let sb_off = sign_bit % 32;
                let neg = self.0.get(sb_idx).cloned().unwrap_or(0) >> sb_off != 0;
                if neg {
                    // For signed integers, the high bit has value `-2^(N-1)` instead of `2^(N-1)`.
                    // So when the high bit is set, the value of `i` needs an adjustment of `-2^N`
                    // to go from unsigned to signed interpretation.
                    i -= BigInt::from(1) << sz.bits();
                }
                i
            },
            _ => panic!("expected an integer type, but got {:?}", ty),
        }
    }
}

pub trait AsBits {
    /// Convert `self` to `Bits`, interned in circuit `c`.  `width` is the size of the output;
    /// signed integers should be sign-extended to this width before conversion.
    fn as_bits<'a, C>(&self, c: &C, width: IntSize) -> Bits<'a>
    where C: CircuitTrait<'a> + ?Sized;

    fn as_any<'a>(&'a self) -> AnyAsBits<'a>;
}

#[derive(Clone, Copy, Debug)]
pub enum AnyAsBits<'a> {
    Bits(Bits<'a>),
    BigUint(&'a BigUint),
    BigInt(&'a BigInt),
    U32(u32),
    U64(u64),
}

impl AsBits for Bits<'_> {
    fn as_bits<'a, C>(&self, c: &C, _width: IntSize) -> Bits<'a>
    where C: CircuitTrait<'a> + ?Sized {
        c.intern_bits(self.0)
    }

    fn as_any<'a>(&'a self) -> AnyAsBits<'a> {
        AnyAsBits::Bits(*self)
    }
}

impl AsBits for BigUint {
    fn as_bits<'a, C>(&self, c: &C, _width: IntSize) -> Bits<'a>
    where C: CircuitTrait<'a> + ?Sized {
        c.intern_bits(&self.to_u32_digits())
    }

    fn as_any<'a>(&'a self) -> AnyAsBits<'a> {
        AnyAsBits::BigUint(self)
    }
}

impl AsBits for u8 {
    fn as_bits<'a, C>(&self, c: &C, width: IntSize) -> Bits<'a>
    where C: CircuitTrait<'a> + ?Sized {
        (*self as u32).as_bits(c, width)
    }

    fn as_any<'a>(&'a self) -> AnyAsBits<'a> {
        AnyAsBits::U32(*self as u32)
    }
}

impl AsBits for u16 {
    fn as_bits<'a, C>(&self, c: &C, width: IntSize) -> Bits<'a>
    where C: CircuitTrait<'a> + ?Sized {
        (*self as u32).as_bits(c, width)
    }

    fn as_any<'a>(&'a self) -> AnyAsBits<'a> {
        AnyAsBits::U32(*self as u32)
    }
}

impl AsBits for u32 {
    fn as_bits<'a, C>(&self, c: &C, _width: IntSize) -> Bits<'a>
    where C: CircuitTrait<'a> + ?Sized {
        c.intern_bits(&[*self])
    }

    fn as_any<'a>(&'a self) -> AnyAsBits<'a> {
        AnyAsBits::U32(*self)
    }
}

impl AsBits for u64 {
    fn as_bits<'a, C>(&self, c: &C, _width: IntSize) -> Bits<'a>
    where C: CircuitTrait<'a> + ?Sized {
        let lo = *self as u32;
        let hi = (*self >> 32) as u32;
        c.intern_bits(&[lo, hi])
    }

    fn as_any<'a>(&'a self) -> AnyAsBits<'a> {
        AnyAsBits::U64(*self)
    }
}

impl AsBits for BigInt {
    fn as_bits<'a, C>(&self, c: &C, width: IntSize) -> Bits<'a>
    where C: CircuitTrait<'a> + ?Sized {
        let mask = (BigInt::from(1) << width.bits()) - 1;
        let (sign, val) = (self & &mask).into_parts();
        assert!(sign != Sign::Minus);
        val.as_bits(c, width)
    }

    fn as_any<'a>(&'a self) -> AnyAsBits<'a> {
        AnyAsBits::BigInt(self)
    }
}

impl AsBits for i32 {
    fn as_bits<'a, C>(&self, c: &C, width: IntSize) -> Bits<'a>
    where C: CircuitTrait<'a> + ?Sized {
        if width == IntSize(32) {
            (*self as u32).as_bits(c, width)
        } else {
            BigInt::from(*self).as_bits(c, width)
        }
    }

    fn as_any<'a>(&'a self) -> AnyAsBits<'a> {
        AnyAsBits::U32(*self as u32)
    }
}

impl AsBits for i64 {
    fn as_bits<'a, C>(&self, c: &C, width: IntSize) -> Bits<'a>
    where C: CircuitTrait<'a> + ?Sized {
        if width == IntSize(64) {
            (*self as u64).as_bits(c, width)
        } else {
            BigInt::from(*self).as_bits(c, width)
        }
    }

    fn as_any<'a>(&'a self) -> AnyAsBits<'a> {
        AnyAsBits::U64(*self as u64)
    }
}

impl AsBits for AnyAsBits<'_> {
    fn as_bits<'a, C>(&self, c: &C, width: IntSize) -> Bits<'a>
    where C: CircuitTrait<'a> + ?Sized {
        match *self {
            AnyAsBits::Bits(x) => x.as_bits(c, width),
            AnyAsBits::BigUint(x) => x.as_bits(c, width),
            AnyAsBits::BigInt(x) => x.as_bits(c, width),
            AnyAsBits::U32(x) => x.as_bits(c, width),
            AnyAsBits::U64(x) => x.as_bits(c, width),
        }
    }

    fn as_any<'a>(&'a self) -> AnyAsBits<'a> {
        *self
    }
}

#[derive(Clone, Copy, Debug)]
pub struct BitsToIntError {
    actual: u16,
    expected: u16,
}

impl fmt::Display for BitsToIntError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(
            fmt,
            "too many bits for target type: got {}, but expected at most {}",
            self.actual, self.expected,
        )
    }
}

impl TryFrom<Bits<'_>> for u32 {
    type Error = BitsToIntError;
    fn try_from(bits: Bits) -> Result<u32, BitsToIntError> {
        if bits.width() > 32 {
            return Err(BitsToIntError { actual: bits.width(), expected: 32 });
        }
        Ok(bits.0[0])
    }
}

impl TryFrom<Bits<'_>> for u64 {
    type Error = BitsToIntError;
    fn try_from(bits: Bits) -> Result<u64, BitsToIntError> {
        if bits.width() > 64 {
            return Err(BitsToIntError { actual: bits.width(), expected: 64 });
        }
        Ok(bits.0[0] as u64 | (bits.0[1] as u64) << 32)
    }
}
