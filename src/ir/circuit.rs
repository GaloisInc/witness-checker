use std::cell::{Cell, RefCell};
use std::collections::HashSet;
use std::hash::{Hash, Hasher};
use std::fmt;
use std::ops::Deref;
use bumpalo::Bump;

pub struct Circuit<'a> {
    arena: &'a Bump,
    intern: RefCell<HashSet<&'a Gate<'a>>>,
    input_tys: Vec<TyKind>,
}

impl<'a> Circuit<'a> {
    pub fn new(arena: &'a Bump, input_tys: Vec<TyKind>) -> Circuit<'a> {
        Circuit {
            arena,
            intern: RefCell::new(HashSet::new()),
            input_tys,
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

    fn mk_gate(&self, ty: Ty, kind: GateKind<'a>) -> Wire<'a> {
        Wire(self.intern(Gate { ty, kind }))
    }

    pub fn lit(&self, ty: Ty, val: u64) -> Wire<'a> {
        self.mk_gate(ty, GateKind::Lit(val))
    }

    pub fn secret(&self, arg: Wire<'a>) -> Wire<'a> {
        if arg.ty.secret {
            return arg;
        }

        self.mk_gate(Ty::new(arg.ty.kind, true), GateKind::Secret(arg))
    }

    pub fn input(&self, idx: usize) -> Wire<'a> {
        self.mk_gate(Ty::new(self.input_tys[idx], true), GateKind::Input(idx))
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
        assert!(a.ty.kind == b.ty.kind);
        if a.ty.secret || b.ty.secret {
            self.mk_gate(
                Ty::new(a.ty.kind, true),
                GateKind::Binary(op, self.secret(a), self.secret(b)),
            )
        } else {
            self.mk_gate(
                Ty::new(a.ty.kind, false),
                GateKind::Binary(op, a, b),
            )
        }
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
        if a.ty.secret || b.ty.secret {
            self.mk_gate(
                Ty::new(a.ty.kind, true),
                GateKind::Shift(op, self.secret(a), self.secret(b)),
            )
        } else {
            self.mk_gate(
                Ty::new(a.ty.kind, false),
                GateKind::Shift(op, a, b),
            )
        }
    }

    pub fn shl(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.shift(ShiftOp::Shl, a, b)
    }

    pub fn shr(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.shift(ShiftOp::Shr, a, b)
    }

    pub fn compare(&self, op: CmpOp, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        assert!(a.ty.kind == b.ty.kind);
        if a.ty.secret || b.ty.secret {
            self.mk_gate(
                Ty::new(TyKind::Bool, true),
                GateKind::Compare(op, self.secret(a), self.secret(b)),
            )
        } else {
            self.mk_gate(
                Ty::new(TyKind::Bool, false),
                GateKind::Compare(op, a, b),
            )
        }
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
        if c.ty.secret || t.ty.secret || e.ty.secret {
            self.mk_gate(
                Ty::new(t.ty.kind, true),
                GateKind::Mux(
                    self.secret(c),
                    self.secret(t),
                    self.secret(e),
                ),
            )
        } else {
            self.mk_gate(
                Ty::new(t.ty.kind, false),
                GateKind::Mux(c, t, e),
            )
        }
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
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Ty {
    pub kind: TyKind,
    pub secret: bool,
}

impl Ty {
    pub fn new(kind: TyKind, secret: bool) -> Ty {
        Ty { kind, secret }
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
    /// Convert a public value to a secret one.
    Secret(Wire<'a>),
    /// Retrieve a secret input, given its index.
    Input(usize),
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


#[derive(Clone, Copy)]
pub struct Wire<'a>(&'a Gate<'a>);

impl<'a> PartialEq for Wire<'a> {
    fn eq(&self, other: &Wire<'a>) -> bool {
        self.0 as *const _ == other.0 as *const _
    }

    fn ne(&self, other: &Wire<'a>) -> bool {
        self.0 as *const _ != other.0 as *const _
    }
}

impl Eq for Wire<'_> {}

impl<'a> Hash for Wire<'a> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.0 as *const Gate).hash(state)
    }
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

impl<'a> Deref for Wire<'a> {
    type Target = Gate<'a>;
    fn deref(&self) -> &Gate<'a> {
        self.0
    }
}
