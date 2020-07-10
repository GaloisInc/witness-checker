use std::any;
use std::collections::HashMap;
use scale_isa::types as instr;
use scale_isa::types::{
    Operand, Instruction,
    Imm, RegClearModp, RegClearRegint, RegSecretBit, RegSecretModp, RegSecretRegint,
};
use crate::ir::circuit::{Wire, Gate, TyKind, GateKind, UnOp, BinOp, ShiftOp, CmpOp};


trait OperandKind: Sized {
    fn from_u32(x: u32) -> Self;

    fn pack(self) -> Operand;

    fn unpack_from(op: &Operand) -> Self {
        Self::try_unpack_from(op).unwrap_or_else(|| {
            panic!("expected {}, but got {:?}", any::type_name::<Self>(), op);
        })
    }

    fn try_unpack_from(op: &Operand) -> Option<Self>;
}

macro_rules! impl_operand_kind {
    ($T:ident) => {
        impl OperandKind for $T {
            fn from_u32(x: u32) -> Self {
                $T::new(x)
            }

            fn pack(self) -> Operand {
                Operand::$T(self)
            }

            fn try_unpack_from(op: &Operand) -> Option<Self> {
                match *op {
                    Operand::$T(x) => Some(x),
                    _ => None,
                }
            }
        }
    };
}

impl_operand_kind!(Imm);
impl_operand_kind!(RegClearModp);
impl_operand_kind!(RegClearRegint);
impl_operand_kind!(RegSecretBit);
impl_operand_kind!(RegSecretModp);
impl_operand_kind!(RegSecretRegint);

trait OperandExt {
    fn unpack<T: OperandKind>(&self) -> T;
    fn try_unpack<T: OperandKind>(&self) -> Option<T>;
}

impl OperandExt for Operand {
    fn unpack<T: OperandKind>(&self) -> T {
        T::unpack_from(self)
    }

    fn try_unpack<T: OperandKind>(&self) -> Option<T> {
        T::try_unpack_from(self)
    }
}


pub struct Backend<'a> {
    operand_map: HashMap<Wire<'a>, Operand>,
    instrs: Vec<Instruction>,
    next_reg: u32,
}

impl<'a> Backend<'a> {
    pub fn new() -> Backend<'a> {
        Backend {
            operand_map: HashMap::new(),
            instrs: Vec::new(),
            next_reg: 0,
        }
    }

    fn fresh<T: OperandKind>(&mut self) -> T {
        let x = self.next_reg;
        self.next_reg += 1;
        T::from_u32(x)
    }

    pub fn instr(&mut self, instr: Instruction) {
        self.instrs.push(instr);
    }

    pub fn wire(&mut self, wire: Wire<'a>) -> Operand {
        if let Some(operand) = self.operand_map.get(&wire) {
            return operand.clone();
        }

        let gate = &*wire;

        let gate_ty = match gate.kind {
            GateKind::Compare(_, a, _) => a.ty,
            _ => gate.ty
        };

        let operand = match *gate_ty {
            TyKind::Bool => self.gate_bool(gate),
            TyKind::U64 => self.gate_u64(gate),
            k => unimplemented!("TyKind {:?}", k),
        };

        self.operand_map.insert(wire, operand.clone());
        operand
    }

    pub fn finish(self) -> Vec<Instruction> {
        self.instrs
    }


    pub fn reveal(&mut self, x: Operand) -> Operand {
        match x {
            Operand::RegSecretBit(x) => {
                let dest = self.fresh::<RegClearRegint>();
                self.instr(instr::opensbit(0, dest, x));
                dest.pack()
            },
            Operand::RegSecretModp(x) => {
                let dest = self.fresh::<RegClearModp>();
                self.instr(instr::start_open(0, vec![x]));
                self.instr(instr::stop_open(0, vec![dest]));
                dest.pack()
            },
            Operand::RegSecretRegint(x) => {
                let dest = self.fresh::<RegClearRegint>();
                self.instr(instr::opensint(0, dest, x));
                dest.pack()
            },
            x => unimplemented!("unsupported operand {:?} in reveal", x),
        }
    }

    pub fn print(&mut self, x: Operand) {
        match x {
            Operand::RegClearModp(x) => {
                self.instr(instr::print_reg(0, x));
            },
            Operand::RegClearRegint(x) => {
                self.instr(instr::print_int(0, x));
            },
            x => unimplemented!("unsupported operand {:?} in print", x),
        }
    }

    pub fn print_str(&mut self, s: &str) {
        for c in s.chars() {
            self.instr(instr::print_char(0, Imm::new(c as u32)));
        }
    }


    fn lit(&self, wire: Wire<'a>) -> Option<u64> {
        match wire.kind {
            GateKind::Lit(x, _) => Some(x),
            _ => None,
        }
    }

    fn gate_bool(&mut self, gate: &Gate<'a>) -> Operand {
        let dest = self.fresh::<RegSecretBit>();
        match gate.kind {
            GateKind::Lit(x, _) => {
                assert!(x == 0 || x == 1, "unsupported literal {} for Bool", x);
                self.instr(instr::ldsbit(0, dest, Imm::from_u32(x as u32)));
            },
            GateKind::Secret(s) => {
                let x = s.val
                    .expect("NYI: generation of SCALE output without witness values");
                assert!(x == 0 || x == 1, "unsupported literal {} for Bool", x);
                self.instr(instr::ldsbit(0, dest, Imm::from_u32(x as u32)));
            },
            GateKind::Unary(op, _a) => {
                match op {
                    // `not(x)` should be lowered to `xor(x, 1)`.
                    UnOp::Not => unimplemented!("UnOp::Not"),
                    _ => unimplemented!("arithmetic ({:?}) on Bool", op),
                }
            },
            GateKind::Binary(op, a, b) => {
                let a = self.wire(a).unpack();
                let b = self.wire(b).unpack();
                match op {
                    BinOp::And => self.instr(instr::andsb(0, dest, a, b)),
                    BinOp::Or => self.instr(instr::orsb(0, dest, a, b)),
                    BinOp::Xor => self.instr(instr::xorsb(0, dest, a, b)),
                    _ => unimplemented!("arithmetic ({:?}) on Bool", op),
                }
            },
            GateKind::Shift(_, _, _) => unimplemented!("Shift on Bool"),
            // `eq(x, y)` should be lowered to `not(xor(x, y))`
            GateKind::Compare(_, _, _) => unimplemented!("Compare on Bool"),
            GateKind::Mux(_, _, _) => unimplemented!("Mux on Bool"),
            GateKind::Cast(a_wire, _) => {
                let a = self.wire(a_wire);
                match *a_wire.ty {
                    TyKind::Bool => return a,
                    TyKind::U64 => {
                        self.instr(instr::bitsint(0, dest, a.unpack(), Imm::new(0)));
                    },
                    _ => unimplemented!("cast to Bool from {:?}", a_wire.ty),
                }
            },
            GateKind::Pack(..) => panic!("SCALE backend does not support Pack"),
            GateKind::Extract(..) => panic!("SCALE backend does not support Extract"),
            GateKind::Gadget(..) => panic!("SCALE backend does not support Gadget"),
        }
        dest.pack()
    }

    fn gate_u64(&mut self, gate: &Gate<'a>) -> Operand {
        match gate.kind {
            GateKind::Lit(x, _) => {
                let dest = self.fresh::<RegSecretRegint>();
                assert!(x <= u32::MAX as u64, "literal {} out of range for", x);
                self.instr(instr::ldsint(0, dest, Imm::from_u32(x as u32)));
                dest.pack()
            },
            GateKind::Secret(s) => {
                let x = s.val
                    .expect("NYI: generation of SCALE output without witness values");
                let dest = self.fresh::<RegSecretRegint>();
                assert!(x <= u32::MAX as u64, "literal {} out of range for", x);
                self.instr(instr::ldsint(0, dest, Imm::from_u32(x as u32)));
                dest.pack()
            },
            GateKind::Unary(op, a) => {
                let dest = self.fresh::<RegSecretRegint>();
                let a = self.wire(a).unpack();
                match op {
                    UnOp::Not => self.instr(instr::invsint(0, dest, a)),
                    UnOp::Neg => self.instr(instr::neg(0, dest, a)),
                }
                dest.pack()
            },
            GateKind::Binary(op, a, b) => {
                let dest = self.fresh::<RegSecretRegint>();
                let a = self.wire(a).unpack();
                let b = self.wire(b).unpack();
                // TODO: use `addsintc` when possible
                match op {
                    BinOp::Add => self.instr(instr::addsint(0, dest, a, b)),
                    BinOp::Sub => self.instr(instr::subsint(0, dest, a, b)),
                    BinOp::Mul => self.instr(instr::mulsint(0, dest, a, b)),
                    BinOp::Div => self.instr(instr::divsint(0, dest, a, b)),
                    BinOp::Mod => unimplemented!("Mod on u64"),
                    BinOp::And => self.instr(instr::andsint(0, dest, a, b)),
                    BinOp::Or => self.instr(instr::orsint(0, dest, a, b)),
                    BinOp::Xor => self.instr(instr::xorsint(0, dest, a, b)),
                }
                dest.pack()
            },
            GateKind::Shift(op, a, b) => {
                let dest = self.fresh::<RegSecretRegint>();
                let a = self.wire(a).unpack();
                let b = self.lit(b).unwrap_or_else(|| {
                    panic!("only shifts by literals (not {:?}) are supported", b);
                });
                assert!(b <= u32::MAX as u64, "shift amount {} out of range", b);
                match op {
                    ShiftOp::Shl => self.instr(instr::shlsint(0, dest, a, Imm::new(b as u32))),
                    ShiftOp::Shr => self.instr(instr::shrsint(0, dest, a, Imm::new(b as u32))),
                }
                dest.pack()
            },
            GateKind::Compare(op, a, b) => {
                let dest = self.fresh::<RegSecretBit>();
                let a = self.wire(a).unpack();
                assert!(
                    self.lit(b) == Some(0),
                    "only comparisons to zero (not {:?}) are supported", b,
                );
                match op {
                    CmpOp::Eq => self.instr(instr::eqzsint(0, dest, a)),
                    CmpOp::Lt => self.instr(instr::ltzsint(0, dest, a)),
                    _ => unimplemented!("comparison ({:?}) on u64", op),
                }
                dest.pack()
            },
            GateKind::Mux(_, _, _) => unimplemented!("Mux on u64"),
            GateKind::Cast(a_wire, _) => {
                let dest = self.fresh::<RegSecretRegint>();
                let a = self.wire(a_wire);
                match *a_wire.ty {
                    TyKind::Bool => {
                        let zero = self.fresh::<RegSecretRegint>();
                        self.instr(instr::ldsint(0, zero, Imm::new(0)));
                        self.instr(instr::sintsbit(0, dest, zero, a.unpack(), Imm::new(0)));
                    },
                    TyKind::U64 => return a,
                    _ => unimplemented!("cast to U64 from {:?}", a_wire.ty),
                }
                dest.pack()
            },
            GateKind::Pack(..) => panic!("SCALE backend does not support Pack"),
            GateKind::Extract(..) => panic!("SCALE backend does not support Extract"),
            GateKind::Gadget(..) => panic!("SCALE backend does not support Gadget"),
        }
    }
}
