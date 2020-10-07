use std::any;
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::fmt;
use std::ops::Deref;
use std::str;
use bumpalo::Bump;

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
    intern_gadget_kind: RefCell<HashMap<String, &'a dyn GadgetKind<'a>>>,
    intern_str: RefCell<HashSet<&'a str>>,

    current_label: Cell<&'a str>,
}

impl<'a> Circuit<'a> {
    pub fn new(arena: &'a Bump) -> Circuit<'a> {
        Circuit {
            arena,
            intern_gate: RefCell::new(HashSet::new()),
            intern_ty: RefCell::new(HashSet::new()),
            intern_wire_list: RefCell::new(HashSet::new()),
            intern_ty_list: RefCell::new(HashSet::new()),
            intern_gadget_kind: RefCell::new(HashMap::new()),
            intern_str: RefCell::new(HashSet::new()),
            current_label: Cell::new(""),
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

    /// Intern a gadget kind so it can be used to construct `Gadget` gates.  It's legal to intern
    /// the same `GadgetKind` more than once, so this can be used inside stateless lowering passes
    /// (among other things).
    pub fn intern_gadget_kind<G: GadgetKind<'a>>(&self, g: G) -> GadgetKindRef<'a> {
        let mut intern = self.intern_gadget_kind.borrow_mut();
        match intern.get(g.name()) {
            Some(&x) => {
                // Check that the interned gadget has the same concrete type as `g`.  If not, then
                // the user has accidentally defined two different gadgets with the same name.
                // Note that if `G` contains data (is non-zero-sized), it may still be possible to
                // have multiple distinct gadget kinds that are not caught by this check.
                assert!(
                    g.type_name() == x.type_name(),
                    "defined multiple distinct gadgets named {:?}: {:?} != {:?}",
                    g.name(), g.type_name(), x.type_name(),
                );
                GadgetKindRef(x)
            },
            None => {
                let g = self.arena.alloc(g);
                intern.insert(g.name().to_owned(), g);
                GadgetKindRef(g)
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
                    *c.ty == TyKind::Bool,
                    "mux condition must be Bool, not {:?}", c.ty,
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

    pub fn lit(&self, ty: Ty<'a>, val: u64) -> Wire<'a> {
        self.gate(GateKind::Lit(val, ty))
    }

    pub fn secret(&self, secret: Secret<'a>) -> Wire<'a> {
        self.gate(GateKind::Secret(secret))
    }

    /// Add a new secret value to the witness, and return a `Wire` that carries that value.
    ///
    /// `val` can be `None` if the witness values are unknown, as when the verifier (not the
    /// prover) is generating the circuit.
    pub fn new_secret(&self, ty: Ty<'a>, val: Option<u64>) -> Wire<'a> {
        let secret = Secret(self.arena.alloc(SecretData { ty, val }));
        self.secret(secret)
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
        let old = self.current_label.get();
        let new = self.intern_str(&format!("{}/{}", old, label));
        CellResetGuard::new(&self.current_label, new)
    }
}

/// `PostorderIter` performs a depth-first postorder traversal.  Since it's postorder, we need to
/// distinguish the first visit to a given node (when it gets expanded and its children are pushed)
/// from the second (when the node itself is yielded to the callback).
enum PostorderEntry<'a> {
    Expand(Wire<'a>),
    Yield(Wire<'a>),
}

pub struct PostorderIter<'a> {
    stack: Vec<PostorderEntry<'a>>,
    /// Wires that have already been yielded.  We avoid processing the same wire twice.
    yielded: HashSet<Wire<'a>>,
}

impl<'a> PostorderIter<'a> {
    fn push_expand(&mut self, w: Wire<'a>) {
        self.stack.push(PostorderEntry::Expand(w));
    }
}

impl<'a> Iterator for PostorderIter<'a> {
    type Item = Wire<'a>;
    fn next(&mut self) -> Option<Wire<'a>> {
        while let Some(entry) = self.stack.pop() {
            match entry {
                PostorderEntry::Expand(w) => {
                    // It's possible for a yielded wire to appear in an `Expand` entry, as a wire
                    // may have multiple parents.  We ignore these entries to avoid duplicate work.
                    if self.yielded.contains(&w) {
                        continue;
                    }

                    self.stack.push(PostorderEntry::Yield(w));
                    match w.kind {
                        GateKind::Lit(_, _) => {}
                        GateKind::Secret(_) => {}
                        GateKind::Unary(_, a) => {
                            self.push_expand(a);
                        },
                        GateKind::Binary(_, a, b) => {
                            self.push_expand(b);
                            self.push_expand(a);
                        },
                        GateKind::Shift(_, a, b) => {
                            self.push_expand(b);
                            self.push_expand(a);
                        },
                        GateKind::Compare(_, a, b) => {
                            self.push_expand(b);
                            self.push_expand(a);
                        },
                        GateKind::Mux(c, t, e) => {
                            self.push_expand(e);
                            self.push_expand(t);
                            self.push_expand(c);
                        },
                        GateKind::Cast(w, _) => {
                            self.push_expand(w);
                        },
                        GateKind::Pack(ws) => {
                            for &w in ws.iter().rev() {
                                self.push_expand(w);
                            }
                        },
                        GateKind::Extract(w, _) => {
                            self.push_expand(w);
                        },
                        GateKind::Gadget(_, ws) => {
                            for &w in ws.iter().rev() {
                                self.push_expand(w);
                            }
                        },
                    }
                },

                PostorderEntry::Yield(w) => {
                    let inserted = self.yielded.insert(w);
                    // It's not possible for a yielded wire to appear in a `Yield` entry.  This
                    // would imply that there were once two different `Yield` entries for the same
                    // wire in the stack.  But `Yield` entries correspond to the direct ancestors
                    // of the current node, so two `Yield` entries would imply that the wire is its
                    // own ancestor (a cycle in the circuit).  Cycles are impossible to construct,
                    // since gates are read-only after construction.
                    assert!(inserted);

                    return Some(w);
                },
            }
        }
        None
    }
}

pub fn walk_wires<'a, I>(wires: I) -> PostorderIter<'a>
where I: IntoIterator<Item = Wire<'a>> {
    let mut stack = wires.into_iter().map(PostorderEntry::Expand).collect::<Vec<_>>();
    stack.reverse();
    PostorderIter {
        stack,
        yielded: HashSet::new(),
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


#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum IntSize {
    I8,
    I16,
    I32,
    I64,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum TyKind<'a> {
    Bool,
    Int(IntSize),
    Uint(IntSize),
    Bundle(&'a [Ty<'a>]),
}

impl IntSize {
    pub fn bits(self) -> u8 {
        match self {
            IntSize::I8 => 8,
            IntSize::I16 => 16,
            IntSize::I32 => 32,
            IntSize::I64 => 64,
        }
    }
}

impl TyKind<'_> {
    pub const I8: TyKind<'static> = TyKind::Int(IntSize::I8);
    pub const I16: TyKind<'static> = TyKind::Int(IntSize::I16);
    pub const I32: TyKind<'static> = TyKind::Int(IntSize::I32);
    pub const I64: TyKind<'static> = TyKind::Int(IntSize::I64);
    pub const U8: TyKind<'static> = TyKind::Uint(IntSize::I8);
    pub const U16: TyKind<'static> = TyKind::Uint(IntSize::I16);
    pub const U32: TyKind<'static> = TyKind::Uint(IntSize::I32);
    pub const U64: TyKind<'static> = TyKind::Uint(IntSize::I64);

    pub fn is_integer(&self) -> bool {
        match *self {
            TyKind::Bool => false,
            TyKind::Int(_) => true,
            TyKind::Uint(_) => true,
            TyKind::Bundle(_) => false,
        }
    }

    pub fn integer_size(&self) -> IntSize {
        match *self {
            TyKind::Bool => panic!("Bool has no IntSize"),
            TyKind::Int(sz) => sz,
            TyKind::Uint(sz) => sz,
            TyKind::Bundle(_) => panic!("Bundle has no IntSize"),
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
    Lit(u64, Ty<'a>),
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
            GateKind::Compare(_, _, _) => c.ty(TyKind::Bool),
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

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SecretData<'a> {
    pub ty: Ty<'a>,
    pub val: Option<u64>,
}

declare_interned_pointer! {
    #[derive(Debug)]
    pub struct Ty<'a> => TyKind<'a>;
}


/// Defines a kind of gadget.  Instances of a gadget can be added to a `Circuit` using
/// `define_gadget_kind` and the `Circuit::gadget` constructor.
pub trait GadgetKind<'a>: 'a {
    /// The name of this kind of gadget.  This must be unique among all gadget kinds, as it's used
    /// by backends to recognize supported gadgets.
    fn name(&self) -> &str;

    /// Intern this `GadgetKind` into a new `Circuit`.  This should usually be implemented as
    ///
    ///     fn transfer<'b>(&self, c: &Circuit<'b>) -> GadgetKindRef<'b> {
    ///         c.intern_gadget_kind(self.clone())
    ///     }
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

    /// Returns `std::any::type_name::<Self>()`.  Should not be implemented manually.  This is used
    /// only for debugging, to check for accidental collisions between `name()`s of distinct
    /// `GadgetKind`s.
    fn type_name(&self) -> &'static str {
        any::type_name::<Self>()
    }
}

declare_interned_pointer! {
    pub struct GadgetKindRef<'a> => dyn GadgetKind<'a>;
}

impl<'a> fmt::Debug for GadgetKindRef<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "GadgetKindRef({})", self.name())
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
