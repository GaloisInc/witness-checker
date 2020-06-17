use std::cell::{Cell, RefCell};
use std::collections::HashSet;
use std::hash::{Hash, Hasher};
use std::fmt;
use std::ops::Deref;
use bumpalo::Bump;

/// A high-level arithmetic/boolean circuit.
///
/// If a witness is available, the `Circuit` includes its values.  This allows circuit
/// transformations to make corresponding changes to the witness if necessary.  The witness itself
/// is not represented explicitly, but is accessible through the `GateKind::Secret` gates present
/// in the circuit.  Use the `walk_witness` function to obtain the witness values that are used to
/// compute some set of `Wire`s.
pub struct Circuit<'a> {
    arena: &'a Bump,
    intern: RefCell<HashSet<&'a Gate<'a>>>,
}

impl<'a> Circuit<'a> {
    pub fn new(arena: &'a Bump) -> Circuit<'a> {
        Circuit {
            arena,
            intern: RefCell::new(HashSet::new()),
        }
    }

    pub fn intern(&self, gate: Gate<'a>) -> &'a Gate<'a> {
        let mut intern = self.intern.borrow_mut();
        match intern.get(&gate) {
            Some(x) => x,
            None => {
                let gate = self.arena.alloc(gate);
                intern.insert(gate);
                gate
            },
        }
    }

    pub fn gate(&self, gate: Gate<'a>) -> Wire<'a> {
        Wire(self.intern(gate))
    }

    fn mk_gate(&self, ty: Ty, kind: GateKind<'a>) -> Wire<'a> {
        Wire(self.intern(Gate { ty, kind }))
    }

    pub fn lit(&self, ty: Ty, val: u64) -> Wire<'a> {
        self.mk_gate(ty, GateKind::Lit(val))
    }

    pub fn secret(&self, secret: Secret<'a>) -> Wire<'a> {
        self.mk_gate(secret.ty, GateKind::Secret(secret))
    }

    /// Add a new secret value to the witness, and return a `Wire` that carries that value.
    ///
    /// `val` can be `None` if the witness values are unknown, as when the verifier (not the
    /// prover) is generating the circuit.
    pub fn new_secret(&self, ty: Ty, val: Option<u64>) -> Wire<'a> {
        let secret = Secret(self.arena.alloc(SecretData { ty, val }));
        self.secret(secret)
    }

    pub fn unary(&self, op: UnOp, arg: Wire<'a>) -> Wire<'a> {
        self.mk_gate(arg.ty, GateKind::Unary(op, arg))
    }

    pub fn neg(&self, arg: Wire<'a>) -> Wire<'a> {
        self.unary(UnOp::Neg, arg)
    }

    pub fn not(&self, arg: Wire<'a>) -> Wire<'a> {
        self.unary(UnOp::Not, arg)
    }

    pub fn binary(&self, op: BinOp, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        assert!(
            a.ty.kind == b.ty.kind,
            "type mismatch for {:?}: {:?} != {:?}", op, a.ty.kind, b.ty.kind,
        );
        self.mk_gate(
            Ty::new(a.ty.kind),
            GateKind::Binary(op, a, b),
        )
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
        assert!(b.ty.kind == TyKind::Uint(IntSize::I8));
        self.mk_gate(
            Ty::new(a.ty.kind),
            GateKind::Shift(op, a, b),
        )
    }

    pub fn shl(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.shift(ShiftOp::Shl, a, b)
    }

    pub fn shr(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.shift(ShiftOp::Shr, a, b)
    }

    pub fn compare(&self, op: CmpOp, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        assert!(a.ty.kind == b.ty.kind);
        self.mk_gate(
            Ty::new(TyKind::Bool),
            GateKind::Compare(op, a, b),
        )
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
        assert!(t.ty.kind == e.ty.kind);
        self.mk_gate(
            Ty::new(t.ty.kind),
            GateKind::Mux(c, t, e),
        )
    }

    pub fn cast(&self, w: Wire<'a>, ty: TyKind) -> Wire<'a> {
        self.mk_gate(
            Ty::new(ty),
            GateKind::Cast(w, ty),
        )
    }


    pub fn walk_wires<I, F>(&self, wires: I, mut f: F)
    where I: IntoIterator<Item=Wire<'a>>, F: FnMut(Wire<'a>) {
        // This is a depth-first postorder traversal.  Since it's postorder, we need to distinguish
        // the first visit to a given node (when it gets expanded and its children are pushed)
        // from the second (when the node itself is yielded to the callback).
        enum Entry<'a> {
            Expand(Wire<'a>),
            Yield(Wire<'a>),
        }

        let mut stack = wires.into_iter().map(Entry::Expand).collect::<Vec<_>>();
        stack.reverse();

        // Wires that have already been yielded.  We avoid processing the same wire twice.
        let mut yielded = HashSet::new();

        while let Some(entry) = stack.pop() {
            match entry {
                Entry::Expand(w) => {
                    // It's possible for a yielded wire to appear in an `Expand` entry, as a wire
                    // may have multiple parents.  We ignore these entries to avoid duplicate work.
                    if yielded.contains(&w) {
                        continue;
                    }

                    stack.push(Entry::Yield(w));
                    match w.kind {
                        GateKind::Lit(_) => {}
                        GateKind::Secret(_) => {}
                        GateKind::Unary(_, a) => {
                            stack.push(Entry::Expand(a));
                        },
                        GateKind::Binary(_, a, b) => {
                            stack.push(Entry::Expand(b));
                            stack.push(Entry::Expand(a));
                        },
                        GateKind::Shift(_, a, b) => {
                            stack.push(Entry::Expand(b));
                            stack.push(Entry::Expand(a));
                        },
                        GateKind::Compare(_, a, b) => {
                            stack.push(Entry::Expand(b));
                            stack.push(Entry::Expand(a));
                        },
                        GateKind::Mux(c, t, e) => {
                            stack.push(Entry::Expand(e));
                            stack.push(Entry::Expand(t));
                            stack.push(Entry::Expand(c));
                        },
                        GateKind::Cast(w, _) => {
                            stack.push(Entry::Expand(w));
                        },
                    }
                },

                Entry::Yield(w) => {
                    let inserted = yielded.insert(w);
                    // It's not possible for a yielded wire to appear in a `Yield` entry.  This
                    // would imply that there were once two different `Yield` entries for the same
                    // wire in the stack.  But `Yield` entries correspond to the direct ancestors
                    // of the current node, so two `Yield` entries would imply that the wire is its
                    // own ancestor (a cycle in the circuit).  Cycles are impossible to construct,
                    // since gates are read-only after construction.
                    assert!(inserted);

                    f(w);
                },
            }
        }
    }

    /// Visit all `Secret`s that are used in the computation of `wires`.  Yields each `Secret`
    /// once, in some deterministic order (assuming `wires` itself is deterministic).
    pub fn walk_witness<I, F>(&self, wires: I, mut f: F)
    where I: IntoIterator<Item=Wire<'a>>, F: FnMut(Secret<'a>) {
        // In the normal case where every gate is interned properly, we should visit each distinct
        // `GateKind::Secret` only once, and see each `Secret` only once.  However, this can go
        // wrong if there are multiple `Circuit`s using the same arena but different `intern`
        // tables, and wires from one `Circuit` are referenced in another.  Currently we don't
        // defend against this misuse.
        self.walk_wires(wires, |w| match w.kind {
            GateKind::Secret(s) => f(s),
            _ => {},
        });
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum IntSize {
    I8,
    I16,
    I32,
    I64,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum TyKind {
    Bool,
    Int(IntSize),
    Uint(IntSize),
}

impl TyKind {
    pub const I8: TyKind = TyKind::Int(IntSize::I8);
    pub const I16: TyKind = TyKind::Int(IntSize::I16);
    pub const I32: TyKind = TyKind::Int(IntSize::I32);
    pub const I64: TyKind = TyKind::Int(IntSize::I64);
    pub const U8: TyKind = TyKind::Uint(IntSize::I8);
    pub const U16: TyKind = TyKind::Uint(IntSize::I16);
    pub const U32: TyKind = TyKind::Uint(IntSize::I32);
    pub const U64: TyKind = TyKind::Uint(IntSize::I64);

    pub fn is_integer(&self) -> bool {
        match *self {
            TyKind::Bool => false,
            TyKind::Int(_) => true,
            TyKind::Uint(_) => true,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Ty {
    pub kind: TyKind,
}

impl Ty {
    pub fn new(kind: TyKind) -> Ty {
        Ty { kind }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Gate<'a> {
    pub ty: Ty,
    pub kind: GateKind<'a>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum GateKind<'a> {
    /// A literal/constant value.
    Lit(u64),
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
    Cast(Wire<'a>, TyKind),
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
    pub struct Secret<'a> => SecretData;
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SecretData {
    pub ty: Ty,
    pub val: Option<u64>,
}
