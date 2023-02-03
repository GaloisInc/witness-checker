use std::cmp;
use std::collections::btree_map::{BTreeMap, Entry};
use std::convert::TryFrom;
use std::iter::{self, FromIterator};
use std::mem;
use std::slice;
use log::*;
use num_bigint::BigUint;
use num_traits::Zero;
use crate::eval;
use crate::gadget::arith::WideMul;
use crate::gadget::bit_pack::{ConcatBits, ExtractBits};
use crate::ir::circuit::{
    self, CircuitTrait, CircuitBase, BinOp, CmpOp, GateKind, ShiftOp, TyKind, UnOp, Wire, Ty,
    EraseVisitor, MigrateVisitor, Bits, AsBits,
};


mod arith;
mod ops;
#[cfg(feature = "sieve_ir")]
pub mod sink_sieve_ir_function;
mod wire_alloc;


pub type WireId = u64;

fn type_bits(ty: Ty) -> u64 {
    ty.integer_size().bits() as u64
}

fn as_lit(wire: Wire) -> Option<BigUint> {
    match wire.kind {
        GateKind::Lit(x, _) => Some(x.to_biguint()),
        _ => None,
    }
}


pub type Time = usize;

pub const TEMP: Time = 0;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Source {
    Zero,
    One,
    /// Use `n` sequentially numbered wires starting at `.0`.
    Wires(WireId),
    /// Repeat the wire `.0` `n` times.
    RepWire(WireId),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum AssertNoWrap {
    No,
    Yes,
}

impl AssertNoWrap {
    fn as_bool(self) -> bool {
        self == Self::Yes
    }
}

pub trait Sink {
    fn lit(&mut self, expire: Time, n: u64, bits: Bits) -> WireId;
    /// Obtain `n` private/witness inputs, storing them in the `n` wires starting at `out`.  In
    /// prover mode, `value` should be set to the witness value.
    fn private(&mut self, expire: Time, n: u64, value: Option<Bits>) -> WireId;
    fn copy(&mut self, expire: Time, n: u64, a: WireId) -> WireId;
    fn concat_chunks(&mut self, expire: Time, entries: &[(Source, u64)]) -> WireId;

    /// Compute a bitwise AND of `n` wires starting at `a` with `n` wires starting at `b`, placing
    /// the results in the `n` wires starting at `out`.
    fn and(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId;
    fn or(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId;
    fn xor(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId;
    fn not(&mut self, expire: Time, n: u64, a: WireId) -> WireId;

    fn add(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId;
    /// Add two `n`-bit inputs to produce an `n`-bit output, and assert that the addition does not
    /// wrap around (when inputs are interpreted as unsigned).
    fn add_no_wrap(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId;
    fn sub(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId;
    fn mul(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId;
    fn mul_no_wrap(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId;
    /// Multiply two `n`-bit inputs to produce a `2n`-bit product.
    fn wide_mul(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId;
    fn neg(&mut self, expire: Time, n: u64, a: WireId) -> WireId;

    fn mux(&mut self, expire: Time, n: u64, c: WireId, t: WireId, e: WireId) -> WireId;

    fn assert_zero(&mut self, n: u64, a: WireId);

    /// Try to free wires that were allocated with `expire <= now`
    fn free_expired(&mut self, now: Time);

    /// AND together bits `a .. a + n`, producing a single output bit.
    fn and_all(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
        if n == 0 {
            return self.lit(expire, 1, Bits::one());
        } else if n == 1 {
            return self.copy(expire, 1, a);
        }

        let mut acc = a;
        for i in 1 .. n - 1 {
            acc = self.and(TEMP, 1, acc, a + i);
        }
        self.and(expire, 1, acc, a + n - 1)
    }

    fn add_maybe_no_wrap(
        &mut self,
        expire: Time,
        n: u64,
        a: WireId,
        b: WireId,
        assert_no_wrap: AssertNoWrap,
    ) -> WireId {
        if assert_no_wrap.as_bool() {
            self.add_no_wrap(expire, n, a, b)
        } else {
            self.add(expire, n, a, b)
        }
    }

    fn mul_maybe_no_wrap(
        &mut self,
        expire: Time,
        n: u64,
        a: WireId,
        b: WireId,
        assert_no_wrap: AssertNoWrap,
    ) -> WireId {
        if assert_no_wrap.as_bool() {
            self.mul_no_wrap(expire, n, a, b)
        } else {
            self.mul(expire, n, a, b)
        }
    }
}


pub struct Backend<'w, S> {
    sink: S,
    /// Maps each high-level `Wire` to the `WireId` of the first bit in its representation.  The
    /// number of bits in the representation can be computed from the wire type.
    wire_map: BTreeMap<Wire<'w>, WireId>,
}

impl<'w, S: Sink> Backend<'w, S> {
    pub fn new(sink: S) -> Backend<'w, S> {
        Backend {
            sink,
            wire_map: BTreeMap::new(),
        }
    }

    /// Populate `wire_map` with entries for all the wires in `wires`.  Temporary intermediate
    /// values will not be kept in `wire_map`.  The caller is responsible for removing the entries
    /// from `wire_map`, if desired.
    fn convert_wires(&mut self, c: &impl CircuitTrait<'w>, wires: &[Wire<'w>]) -> Vec<WireId> {
        let order = circuit::walk_wires_filtered(
            wires.iter().cloned(),
            |w| !self.wire_map.contains_key(&w),
        ).collect::<Vec<_>>();

        // For each wire, compute its last use time and whether its `WireIds` must be contiguous.
        let mut last_use_map = BTreeMap::new();
        for (i, &w) in order.iter().enumerate() {
            for v in circuit::wire_deps(w) {
                last_use_map.insert(v, i);
            }
        }

        for &w in wires {
            last_use_map.insert(w, usize::MAX);
        }

        // `last_use[i]` gives the last use time of wire `order[i]`.
        let last_use = order.iter().cloned().map(|w| last_use_map[&w]).collect::<Vec<_>>();
        drop(last_use_map);

        // For cleaning up wires from `wire_map`, group wires into fixed-size blocks to be removed
        // all at once.
        const CLEANUP_BLOCK_SIZE: usize = 1024;
        let mut cleanup_blocks: Vec<Vec<Wire>> = iter::repeat_with(Vec::new)
            .take((order.len() + CLEANUP_BLOCK_SIZE - 1) / CLEANUP_BLOCK_SIZE)
            .collect::<Vec<_>>();
        for (&w, &j) in order.iter().zip(last_use.iter()) {
            // Wires listed in `wires` get a large `last_use` value, indicating they should be kept
            // past the end of the `convert_wires` call.
            if j >= order.len() {
                continue;
            }
            cleanup_blocks[j / CLEANUP_BLOCK_SIZE].push(w);
        }

        // Convert each gate.
        for (i, (&w, &j)) in order.iter().zip(last_use.iter()).enumerate() {
            let wire_id = self.convert_wire(c, j as Time, w);
            trace!("converted: {} = {:?}", wire_id, crate::ir::circuit::DebugDepth(0, &w.kind));
            self.wire_map.insert(w, wire_id);

            // If we just finished a cleanup block, remove all wires in that block from `wire_map`.
            if i % CLEANUP_BLOCK_SIZE == 0 && i > 0 {
                for w in mem::take(&mut cleanup_blocks[i / CLEANUP_BLOCK_SIZE - 1]) {
                    self.wire_map.remove(&w);
                }
            }

            self.sink.free_expired(i as Time);
        }

        // Handle the final cleanup block.
        if order.len() > 0 {
            for w in mem::take(&mut cleanup_blocks[order.len() / CLEANUP_BLOCK_SIZE]) {
                self.wire_map.remove(&w);
            }
        }

        // Gather and return the `WireId`s for the requested `wires`.
        wires.iter().cloned().map(|w| self.wire_map[&w]).collect::<Vec<_>>()
    }

    fn convert_wire(&mut self, c: &impl CircuitTrait<'w>, expire: Time, w: Wire<'w>) -> WireId {
        let n = type_bits(w.ty);
        match w.kind {
            GateKind::Lit(val, ty) => {
                assert!(ty.is_integer());
                self.sink.lit(expire, n, val)
            },
            GateKind::Secret(secret) => {
                assert!(secret.ty.is_integer());
                self.sink.private(expire, n, secret.val())
            },

            GateKind::Erased(_erased) => unimplemented!("Erased"),
            GateKind::Argument(_, _) => unimplemented!("Argument"),

            GateKind::Unary(op, aw) => {
                let a = self.wire_map[&aw];
                match op {
                    UnOp::Neg => self.sink.neg(expire, n, a),
                    UnOp::Not => self.sink.not(expire, n, a),
                }
            },

            GateKind::Binary(op, aw, bw) => {
                let a = self.wire_map[&aw];
                let b = self.wire_map[&bw];
                match op {
                    BinOp::Add => self.sink.add(expire, n, a, b),
                    BinOp::Sub => self.sink.sub(expire, n, a, b),
                    BinOp::Mul => self.sink.mul(expire, n, a, b),
                    // TODO: combine Div and Mod into a single DivMod gadget to allow higher-level
                    // optimizations
                    BinOp::Div | BinOp::Mod => {
                        // Only unsigned division is supported.
                        if !matches!(*aw.ty, TyKind::Uint(_)) {
                            unimplemented!("{:?} for {:?}", op, aw.ty);
                        }

                        let sz = aw.ty.integer_size();
                        let a_val = eval::eval_wire_secret(c, aw);
                        let b_val = eval::eval_wire_secret(c, bw);
                        let (quot_bits, rem_bits) = match (a_val.as_ref(), b_val.as_ref()) {
                            (Some(a_val), Some(b_val)) => {
                                let a_uint = a_val.as_single().unwrap();
                                let b_uint = b_val.as_single().unwrap();
                                let (quot_uint, rem_uint) = if !b_uint.is_zero() {
                                    (a_uint / b_uint, a_uint % b_uint)
                                } else {
                                    (Zero::zero(), a_uint.clone())
                                };
                                (
                                    Some(quot_uint.as_bits(c.as_base(), sz)),
                                    Some(rem_uint.as_bits(c.as_base(), sz)),
                                )
                            },
                            _ => (None, None),
                        };

                        // Add witness variables for quotient and remainder.
                        let (quot_expire, rem_expire) = match op {
                            BinOp::Div => (expire, TEMP),
                            BinOp::Mod => (TEMP, expire),
                            _ => unreachable!(),
                        };
                        let quot = self.sink.private(quot_expire, n, quot_bits);
                        let rem = self.sink.private(rem_expire, n, rem_bits);

                        // Assert: a == quot * b + rem
                        {
                            let quot_times_b = self.sink.mul_no_wrap(TEMP, n, quot, b);
                            let quot_times_b_plus_rem =
                                self.sink.add_no_wrap(TEMP, n, quot_times_b, rem);
                            let eq_bits_inv = self.sink.xor(TEMP, n, a, quot_times_b_plus_rem);
                            self.sink.assert_zero(n, eq_bits_inv);
                        }

                        // Assert: rem < b || b == 0
                        {
                            let rem_ext = self.sink.concat_chunks(TEMP, &[
                                (Source::Wires(rem), n),
                                (Source::Zero, 1),
                            ]);
                            let b_ext = self.sink.concat_chunks(TEMP, &[
                                (Source::Wires(b), n),
                                (Source::Zero, 1),
                            ]);
                            let rem_minus_b_ext = self.sink.sub(TEMP, n + 1, rem_ext, b_ext);
                            // `rem < b` if the sign bit of `rem - b` is set.
                            let rem_lt_b = rem_minus_b_ext + n;
                            let rem_lt_b_inv = self.sink.not(TEMP, 1, rem_lt_b);

                            let b_inv = self.sink.not(TEMP, n, b);
                            let b_zero = self.sink.and_all(TEMP, n, b_inv);
                            let b_zero_inv = self.sink.not(TEMP, 1, b_zero);

                            let ok_inv = self.sink.and(TEMP, 1, rem_lt_b_inv, b_zero_inv);
                            self.sink.assert_zero(1, ok_inv);
                        }

                        match op {
                            BinOp::Div => quot,
                            BinOp::Mod => rem,
                            _ => unreachable!(),
                        }
                    },
                    BinOp::And => self.sink.and(expire, n, a, b),
                    BinOp::Or => self.sink.or(expire, n, a, b),
                    BinOp::Xor => self.sink.xor(expire, n, a, b),
                }
            },

            GateKind::Shift(op, val_wire, amount_wire) => {
                let val = self.wire_map[&val_wire];

                let amount = as_lit(amount_wire).unwrap_or_else(|| {
                    panic!("only shifts by literals are supported (not {:?})", amount_wire);
                });
                let amount = u64::try_from(&amount).unwrap_or_else(|_| {
                    panic!("shift amount {:?} out of range", amount);
                });
                let amount = cmp::min(amount, n);

                match (op, *val_wire.ty) {
                    (ShiftOp::Shl, _) => {
                        self.sink.concat_chunks(expire, &[
                            (Source::Zero, amount),
                            (Source::Wires(val), n - amount),
                        ])
                    },
                    (ShiftOp::Shr, TyKind::Uint(_)) => {
                        self.sink.concat_chunks(expire, &[
                            (Source::Wires(val + amount), n - amount),
                            (Source::Zero, amount),
                        ])
                    },
                    (ShiftOp::Shr, TyKind::Int(_)) => {
                        let sign = val + n - 1;
                        self.sink.concat_chunks(expire, &[
                            (Source::Wires(val + amount), n - amount),
                            (Source::RepWire(sign), amount),
                        ])
                    },
                    _ => unimplemented!("Shift({:?}) by {:?}", op, val_wire.ty),
                }
            },

            GateKind::Compare(op, aw, bw) if as_lit(bw).map_or(false, |x| x.is_zero()) => {
                let a = self.wire_map[&aw];
                let m = type_bits(aw.ty);
                let sign = a + m - 1;
                let is_signed = match *aw.ty {
                    TyKind::Int(_) => true,
                    TyKind::Uint(_) => false,
                    _ => unimplemented!("Compare of {:?}", aw.ty),
                };
                match (op, is_signed) {
                    (CmpOp::Eq, _) |
                    // In unsigned arithmetic, `a <= 0` = `a == 0`
                    (CmpOp::Le, false) => {
                        let a_inv = self.sink.not(TEMP, m, a);
                        self.sink.and_all(expire, m, a_inv)
                    },
                    (CmpOp::Ne, _) |
                    // In unsigned arithmetic, `a > 0` = `a != 0`
                    (CmpOp::Gt, false) => {
                        let a_inv = self.sink.not(TEMP, m, a);
                        let out_inv = self.sink.and_all(TEMP, m, a_inv);
                        self.sink.not(expire, 1, out_inv)
                    },
                    (CmpOp::Lt, true) => {
                        // `a < 0` if the sign bit is 1
                        self.sink.copy(expire, 1, sign)
                    },
                    (CmpOp::Lt, false) => {
                        // For unsigned comparisons, `a < 0` is always false.
                        self.sink.lit(expire, 1, Bits::zero())
                    },
                    (CmpOp::Ge, true) => {
                        // `a >= 0` if the sign bit is 0
                        self.sink.not(expire, 1, sign)
                    },
                    (CmpOp::Ge, false) => {
                        self.sink.lit(expire, 1, Bits::one())
                    },
                    // `Gt` and `Le` are slow cases.
                    (CmpOp::Gt, true) => {
                        // `a > 0` if the sign bit is 0 and the rest of `a` is nonzero.
                        let sign_inv = self.sink.not(TEMP, 1, sign); 
                        let a_inv = self.sink.not(TEMP, m - 1, a);
                        let a_zero = self.sink.and_all(TEMP, m - 1, a_inv);
                        let a_nonzero = self.sink.not(TEMP, 1, a_zero);
                        self.sink.and(expire, 1, sign_inv, a_nonzero)
                    },
                    (CmpOp::Le, true) => {
                        // The inverse of `Gt`.
                        let sign_inv = self.sink.not(TEMP, 1, sign); 
                        let a_inv = self.sink.not(TEMP, m - 1, a);
                        let a_zero = self.sink.and_all(TEMP, m - 1, a_inv);
                        let a_nonzero = self.sink.not(TEMP, 1, a_zero);
                        let out_inv = self.sink.and(TEMP, 1, sign_inv, a_nonzero);
                        self.sink.not(expire, 1, out_inv)
                    },
                }
            },

            GateKind::Compare(op, aw, bw) => {
                let a = self.wire_map[&aw];
                let b = self.wire_map[&bw];
                let m = type_bits(aw.ty);
                match op {
                    CmpOp::Eq => {
                        let ne_bits = self.sink.xor(TEMP, m, a, b);
                        let eq_bits = self.sink.not(TEMP, m, ne_bits);
                        self.sink.and_all(expire, m, eq_bits)
                    },
                    CmpOp::Ne => {
                        let ne_bits = self.sink.xor(TEMP, m, a, b);
                        let eq_bits = self.sink.not(TEMP, m, ne_bits);
                        let eq = self.sink.and_all(TEMP, m, eq_bits);
                        self.sink.not(expire, 1, eq)
                    },
                    _ => {
                        unimplemented!("Compare({:?}) with nonzero rhs", op);
                    },
                }
            },

            GateKind::Mux(cw, tw, ew) => {
                debug_assert_eq!(cw.ty, Ty::bool());
                let c = self.wire_map[&cw];
                let t = self.wire_map[&tw];
                let e = self.wire_map[&ew];
                self.sink.mux(expire, n, c, t, e)
            },

            GateKind::Cast(aw, ty) => {
                let a = self.wire_map[&aw];
                let m = type_bits(aw.ty);

                if n <= m {
                    // Truncate `a` (of width `m`) to width `n`.
                    self.sink.copy(expire, n, a)
                } else {
                    // Zero- or sign-extend `a` (of width `m`) to width `n`.
                    let padding = match *aw.ty {
                        TyKind::Uint(_) => Source::Zero,
                        TyKind::Int(_) => Source::RepWire(a + m - 1),
                        _ => unimplemented!("Cast from {:?}", aw.ty),
                    };
                    self.sink.concat_chunks(expire, &[
                        (Source::Wires(a), m),
                        (padding, n - m),
                    ])
                }
            },

            GateKind::Pack(..) => unimplemented!("Pack"),
            GateKind::Extract(..) => unimplemented!("Extract"),

            GateKind::Gadget(gk, ws) => {
                if let Some(_) = gk.cast::<ConcatBits>() {
                    let mut entries = Vec::with_capacity(ws.len());
                    for w in ws {
                        let val = self.wire_map[&w];
                        let width = type_bits(w.ty);
                        entries.push((Source::Wires(val), width));
                    }
                    self.sink.concat_chunks(expire, &entries)
                } else if let Some(g) = gk.cast::<ExtractBits>() {
                    debug_assert!(ws.len() == 1);
                    debug_assert_eq!((g.end - g.start) as u64, n);
                    let w = ws[0];
                    let val = self.wire_map[&w];
                    self.sink.copy(expire, n, val + g.start as u64)
                } else if gk.is::<WideMul>() {
                    debug_assert!(ws.len() == 2);
                    debug_assert_eq!(ws[0].ty, ws[1].ty);
                    let m = type_bits(ws[0].ty);
                    debug_assert_eq!(m * 2, n);
                    let a = self.wire_map[&ws[0]];
                    let b = self.wire_map[&ws[1]];
                    self.sink.wide_mul(expire, m, a, b)
                } else {
                    unimplemented!("Gadget({})", gk.name());
                }
            },

            GateKind::Call(..) => todo!("Call"),
        }
    }

    pub fn post_erase(&mut self, v: &mut EraseVisitor<'w>) {
        use crate::ir::migrate::Visitor as _;
        // Each entry `(old, new)` in `v.erased()` indicates that wire `old` was replaced with the
        // new `Erased` wire `new`.  In each case, we construct (or otherwise obtain) a `ReprId`
        // for `old` and copy it into `wire_map[new]` as well.
        let (old_wires, new_wires): (Vec<_>, Vec<_>) = v.erased().iter().cloned().unzip();
        let old_reprs = self.convert_wires(v.new_circuit(), &old_wires);
        for (old_repr, new_wire) in old_reprs.into_iter().zip(new_wires.into_iter()) {
            assert!(!self.wire_map.contains_key(&new_wire));
            self.wire_map.insert(new_wire, old_repr);
        }
    }

    pub fn post_migrate(&mut self, v: &mut MigrateVisitor<'w, 'w>) {
        use crate::ir::migrate::Visitor as _;

        let old_wire_map = mem::take(&mut self.wire_map);

        for (old_wire, old_repr) in old_wire_map {
            let new_wire = match v.visit_wire_weak(old_wire) {
                Some(x) => x,
                None => {
                    // Wire is no longer accessible.  Notify the sink to free it.
                    // TODO: self.sink.free_wires(old_repr);
                    continue;
                },
            };
            self.wire_map.insert(new_wire, old_repr);
        }
    }

    pub fn enforce_true(&mut self, c: &impl CircuitTrait<'w>, w: Wire<'w>) {
        let wire_ids = self.convert_wires(c, &[w]);
        let w = wire_ids[0];
        let w_inv = self.sink.not(TEMP, 1, w);
        self.sink.assert_zero(1, w_inv);
    }

    pub fn finish(self) -> S {
        self.sink
    }
}


#[cfg(test)]
mod test {
    use std::collections::{HashMap, HashSet};
    use crate::back::UsePlugins;
    use crate::ir::circuit::{
        Circuit, CircuitFilter, CircuitExt, DynCircuit, FilterNil, Arenas, Wire, Ty, TyKind,
        IntSize,
    };
    use super::*;

    #[derive(Default)]
    pub struct TestSink {
        pub m: HashMap<WireId, bool>,
        pub next: WireId,
        pub expire_map: BTreeMap<Time, Vec<WireId>>,
        pub count_and: u64,
        pub count_or: u64,
        pub count_xor: u64,
        pub count_not: u64,
    }

    impl TestSink {
        pub fn get(&self, w: WireId) -> bool {
            self.m.get(&w).cloned()
                .unwrap_or_else(|| panic!("accessed wire {} before definition", w))
        }

        pub fn get_uint(&self, n: u64, w: WireId) -> BigUint {
            let bits = (0 .. n).map(|i| self.get(w + i) as u8).collect::<Vec<_>>();
            BigUint::from_radix_le(&bits, 2).unwrap()
        }

        fn alloc(
            &mut self,
            expire: Time,
            n: u64,
        ) -> WireId {
            let w = self.next;
            self.next += n;

            let mut expire_list = self.expire_map.entry(expire).or_insert_with(Vec::new);
            for i in 0 ..n {
                expire_list.push(w + i);
            }

            w
        }

        fn set(&mut self, w: WireId, val: bool) {
            let old = self.m.insert(w, val);
            assert!(old.is_none());
        }

        pub fn init(
            &mut self,
            expire: Time,
            n: u64,
            mut f: impl FnMut(&mut Self, u64) -> bool,
            desc: std::fmt::Arguments,
        ) -> WireId {
            let w = self.alloc(expire, n);
            for i in 0 .. n {
                let val = f(self, i);
                trace!("{} = {}[{}] = {}", w + i, desc, i, val);
                self.set(w + i, val);
            }
            w
        }
    }

    impl Sink for TestSink {
        fn lit(&mut self, expire: Time, n: u64, bits: Bits) -> WireId {
            self.init(expire, n, |_, i| bits.get(i as usize),
                format_args!("lit({:?})", bits))
        }
        fn private(&mut self, expire: Time, n: u64, value: Option<Bits>) -> WireId {
            let bits = value.unwrap();
            self.init(expire, n, |_, i| bits.get(i as usize),
                format_args!("private({:?})", bits))
        }
        fn copy(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
            self.init(expire, n, |slf, i| slf.get(a + i),
                format_args!("copy({})", a))
        }
        fn concat_chunks(&mut self, expire: Time, entries: &[(Source, u64)]) -> WireId {
            let w = self.alloc(expire, entries.iter().map(|&(_, m)| m).sum());
            let mut off = 0;
            for &(src, n) in entries {
                for i in 0 .. n {
                    let val = match src {
                        Source::Zero => false,
                        Source::One => true,
                        Source::Wires(w2) => self.get(w2 + i),
                        Source::RepWire(w2) => self.get(w2),
                    };
                    trace!("{} = chunks[{}] = {:?}[{}] = {}",
                        w + off + i, off + i, src, i, val);
                    self.set(w + off + i, val);
                }
                off += n;
            }
            w
        }

        fn and(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            self.count_and += n;
            self.init(expire, n, |slf, i| slf.get(a + i) & slf.get(b + i),
                format_args!("and({}, {})", a, b))
        }
        fn or(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            self.count_or += n;
            self.init(expire, n, |slf, i| slf.get(a + i) | slf.get(b + i),
                format_args!("or({}, {})", a, b))
        }
        fn xor(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            self.count_xor += n;
            self.init(expire, n, |slf, i| slf.get(a + i) ^ slf.get(b + i),
                format_args!("xor({}, {})", a, b))
        }
        fn not(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
            self.count_not += n;
            self.init(expire, n, |slf, i| !slf.get(a + i),
                format_args!("not({})", a))
        }

        fn add(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            let a_uint = self.get_uint(n, a);
            let b_uint = self.get_uint(n, b);
            let out_uint = a_uint + b_uint;
            self.init(expire, n, |_, i| out_uint.bit(i),
                format_args!("add({}, {})", a, b))
        }
        fn add_no_wrap(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            let a_uint = self.get_uint(n, a);
            let b_uint = self.get_uint(n, b);
            let out_uint = a_uint + b_uint;
            let out = self.init(expire, n + 1, |_, i| out_uint.bit(i),
                format_args!("add_no_wrap({}, {})", a, b));
            // The highest (carry out) bit must be zero.
            self.assert_zero(1, out + n);
            out
        }
        fn sub(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            let a_uint = self.get_uint(n, a);
            let b_uint = self.get_uint(n, b);
            let out_uint = (BigUint::from(1_u64) << n) + a_uint - b_uint;
            self.init(expire, n, |_, i| out_uint.bit(i),
                format_args!("sub({}, {})", a, b))
        }
        fn mul(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            let a_uint = self.get_uint(n, a);
            let b_uint = self.get_uint(n, b);
            let out_uint = a_uint * b_uint;
            self.init(expire, n, |_, i| out_uint.bit(i),
                format_args!("mul({}, {})", a, b))
        }
        fn mul_no_wrap(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            let a_uint = self.get_uint(n, a);
            let b_uint = self.get_uint(n, b);
            let out_uint = a_uint * b_uint;
            let out = self.init(expire, 2 * n, |_, i| out_uint.bit(i),
                format_args!("mul_no_wrap({}, {})", a, b));
            // The high bits must all be zero.
            self.assert_zero(n, out + n);
            out
        }
        fn wide_mul(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            let a_uint = self.get_uint(n, a);
            let b_uint = self.get_uint(n, b);
            let out_uint = a_uint * b_uint;
            self.init(expire, 2 * n, |_, i| out_uint.bit(i),
                format_args!("wide_mul({}, {})", a, b))
        }
        fn neg(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
            let a_uint = self.get_uint(n, a);
            let out_uint = (a_uint ^ ((BigUint::from(1_u64) << n) - 1_u64)) + 1_u64;
            self.init(expire, n, |_, i| out_uint.bit(i),
                format_args!("neg({})", a))
        }

        fn mux(&mut self, expire: Time, n: u64, c: WireId, t: WireId, e: WireId) -> WireId {
            let c_uint = self.get_uint(1, c);
            let t_uint = self.get_uint(n, t);
            let e_uint = self.get_uint(n, e);
            let out_uint = if !c_uint.is_zero() { t_uint } else { e_uint };
            self.init(expire, n, |_, i| out_uint.bit(i),
                format_args!("mux({}, {}, {})", c, t, e))
        }

        fn assert_zero(&mut self, n: u64, a: WireId) {
            for i in 0 .. n {
                trace!("assert_zero({}) = {}", a + i, self.get(a + i));
                assert!(!self.get(a + i));
            }
        }

        fn free_expired(&mut self, now: Time) {
            let keys = self.expire_map.range(..= now).map(|(&k, _)| k).collect::<Vec<_>>();
            for k in keys {
                for w in self.expire_map.remove(&k).unwrap() {
                    trace!("expired: {}", w);
                    let old = self.m.remove(&w);
                    assert!(old.is_some());
                }
            }
        }
    }


    #[derive(Default)]
    pub struct TestArithSink {
        pub inner: TestSink,
        // For testing, it's useful to be able to override which input sizes use Karatsuba
        // mul/wide_mul vs the simple version.
        pub use_karatsuba_sizes: HashSet<u64>,
        pub use_karatsuba_sizes_wide: HashSet<u64>,
    }

    impl Sink for TestArithSink {
        fn lit(&mut self, expire: Time, n: u64, bits: Bits) -> WireId {
            self.inner.lit(expire, n, bits)
        }
        fn private(&mut self, expire: Time, n: u64, value: Option<Bits>) -> WireId {
            self.inner.private(expire, n, value)
        }
        fn copy(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
            self.inner.copy(expire, n, a)
        }
        fn concat_chunks(&mut self, expire: Time, entries: &[(Source, u64)]) -> WireId {
            self.inner.concat_chunks(expire, entries)
        }

        fn and(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            self.inner.and(expire, n, a, b)
        }
        fn or(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            self.inner.or(expire, n, a, b)
        }
        fn xor(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            self.inner.xor(expire, n, a, b)
        }
        fn not(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
            self.inner.not(expire, n, a)
        }

        fn add(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            arith::add(self, expire, n, a, b, AssertNoWrap::No)
        }
        fn add_no_wrap(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            arith::add(self, expire, n, a, b, AssertNoWrap::Yes)
        }
        fn sub(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            arith::sub(self, expire, n, a, b)
        }
        fn mul(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            if self.use_karatsuba_sizes.contains(&n) {
                arith::mul_karatsuba(self, expire, n, a, b, AssertNoWrap::No)
            } else {
                arith::mul_simple(self, expire, n, a, b, AssertNoWrap::No)
            }
        }
        fn mul_no_wrap(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            if self.use_karatsuba_sizes.contains(&n) {
                arith::mul_karatsuba(self, expire, n, a, b, AssertNoWrap::Yes)
            } else {
                arith::mul_simple(self, expire, n, a, b, AssertNoWrap::Yes)
            }
        }
        fn wide_mul(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
            if self.use_karatsuba_sizes_wide.contains(&n) {
                arith::wide_mul_karatsuba(self, expire, n, a, b)
            } else {
                arith::wide_mul_simple(self, expire, n, a, b)
            }
        }
        fn neg(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
            arith::neg(self, expire, n, a)
        }

        fn mux(&mut self, expire: Time, n: u64, c: WireId, t: WireId, e: WireId) -> WireId {
            self.inner.mux(expire, n, c, t, e)
        }

        fn assert_zero(&mut self, n: u64, a: WireId) {
            self.inner.assert_zero(n, a);
        }

        fn free_expired(&mut self, now: Time) {
            self.inner.free_expired(now);
        }
    }


    fn test_gate_common<'a, const N: usize>(
        c: &Circuit<'a, impl CircuitFilter<'a> + 'a>,
        input_bits: [i16; N],
        mut f: impl FnMut(&DynCircuit<'a>, [Wire<'a>; N]) -> Wire<'a>,
        mut enforce_true: impl FnMut(Wire<'a>),
    ) {
        let total_bits = input_bits.iter().cloned().map(|n| n.abs() as u16).sum::<u16>();
        assert!(total_bits < 64);
        for mut x in 0 .. (1_u64 << total_bits) {
            let mut inputs = Vec::with_capacity(input_bits.len());
            for &n in &input_bits {
                let (signed, n) = (n < 0, n.abs() as u16);
                let ty = if !signed {
                    c.ty(TyKind::Uint(IntSize(n)))
                } else {
                    c.ty(TyKind::Int(IntSize(n)))
                };
                let val = x & ((1 << n) - 1);
                x >>= n;
                inputs.push(c.new_secret_wire_init(ty, || val));
            }
            let inputs = *<&[_; N]>::try_from(&inputs as &[_]).unwrap();
            let out = f(c, inputs);

            let val = eval::eval_wire_secret(c, out).unwrap().unwrap_single().unwrap();
            let ok = c.eq(out, c.lit(out.ty, val));
            let ok_val = eval::eval_wire_secret(c, ok).unwrap().unwrap_single().unwrap();
            assert_eq!(ok_val, 1_u64.into());

            enforce_true(ok);
        }
    }

    fn test_gate_with_arith_sink<const N: usize>(
        arith_sink: TestArithSink,
        input_bits: [i16; N],
        skip_v2_eval: bool,
        mut f: impl for<'a> FnMut(&DynCircuit<'a>, [Wire<'a>; N]) -> Wire<'a>,
    ) {
        let arenas = Arenas::new();
        let c = Circuit::new(&arenas, true, FilterNil);
        let mut backend = Backend::new(TestSink::default());
        let mut arith_backend = Backend::new(arith_sink);

        #[cfg(feature = "sieve_ir")]
        let mut sieve_ir_backend = {
            use zki_sieve::producers::sink::MemorySink;
            let sink = MemorySink::default();
            let sink = sink_sieve_ir_function::SieveIrV1Sink::new(sink, UsePlugins::all());
            Backend::new(sink)
        };
        #[cfg(feature = "sieve_ir")]
        let mut sieve_ir_v2_backend = {
            use zki_sieve_v3::producers::sink::MemorySink;
            let sink = MemorySink::default();
            let sink = sink_sieve_ir_function::SieveIrV2Sink::new(sink, UsePlugins::all());
            Backend::new(sink)
        };

        test_gate_common(&c, input_bits, f, |w| {
            backend.enforce_true(&c, w);
            arith_backend.enforce_true(&c, w);

            #[cfg(feature = "sieve_ir")]
            sieve_ir_backend.enforce_true(&c, w);

            #[cfg(feature = "sieve_ir")]
            sieve_ir_v2_backend.enforce_true(&c, w);
        });

        #[cfg(feature = "sieve_ir")]
        {
            use zki_sieve::Source;
            use zki_sieve::consumers::evaluator::{Evaluator, PlaintextBackend};
            use zki_sieve::consumers::validator::Validator;
            use zki_sieve::structs::message::Message;
            let sink = sieve_ir_backend.finish().finish();
            let source: Source = sink.into();
            let mut validator = Validator::new_as_prover();
            for msg in source.iter_messages() {
                validator.ingest_message(&msg.unwrap());
            }
            assert_eq!(validator.get_violations(), Vec::<String>::new());
            let mut backend = PlaintextBackend::default();
            let evaluator = Evaluator::from_messages(source.iter_messages(), &mut backend);
            assert_eq!(evaluator.get_violations(), Vec::<String>::new());
        }

        #[cfg(feature = "sieve_ir")]
        if !skip_v2_eval {
            use zki_sieve_v3::Source;
            use zki_sieve_v3::consumers::evaluator::{Evaluator, PlaintextBackend};
            use zki_sieve_v3::consumers::validator::Validator;
            use zki_sieve_v3::structs::function::FunctionBody;
            use zki_sieve_v3::structs::directives::Directive;
            use zki_sieve_v3::structs::message::Message;
            let sink = sieve_ir_v2_backend.finish().finish();
            let source: Source = sink.into();
            let mut validator = Validator::new_as_prover();
            for msg in source.iter_messages() {
                let msg = msg.unwrap();
                validator.ingest_message(&msg);
            }
            assert_eq!(validator.get_violations(), Vec::<String>::new());
            let mut backend = PlaintextBackend::default();
            let evaluator = Evaluator::from_messages(source.iter_messages(), &mut backend);
            assert_eq!(evaluator.get_violations(), Vec::<String>::new());
        }
    }

    fn test_gate<const N: usize>(
        input_bits: [i16; N],
        mut f: impl for<'a> FnMut(&DynCircuit<'a>, [Wire<'a>; N]) -> Wire<'a>,
    ) {
        test_gate_with_arith_sink(TestArithSink::default(), input_bits, false, f)
    }

    fn test_gate_skip_v2_eval<const N: usize>(
        input_bits: [i16; N],
        mut f: impl for<'a> FnMut(&DynCircuit<'a>, [Wire<'a>; N]) -> Wire<'a>,
    ) {
        test_gate_with_arith_sink(TestArithSink::default(), input_bits, true, f)
    }


    #[test]
    fn lit_1() {
        test_gate([], |c, _| c.lit(Ty::bool(), 0));
        test_gate([], |c, _| c.lit(Ty::bool(), 1));
    }


    #[test]
    fn not_1() {
        test_gate([1], |c, [w]| c.not(w));
    }

    #[test]
    fn and_1() {
        test_gate([1, 1], |c, [a, b]| c.and(a, b));
    }

    #[test]
    fn or_1() {
        test_gate([1, 1], |c, [a, b]| c.or(a, b));
    }

    #[test]
    fn xor_1() {
        test_gate([1, 1], |c, [a, b]| c.xor(a, b));
    }

    #[test]
    fn shl_1() {
        test_gate([1, 2], |c, [a, b]| {
            let amount = eval::eval_wire_secret(c, b).unwrap().unwrap_single().unwrap();
            c.shl(a, c.lit(b.ty, amount))
        });
        test_gate([-1, 2], |c, [a, b]| {
            let amount = eval::eval_wire_secret(c, b).unwrap().unwrap_single().unwrap();
            c.shl(a, c.lit(b.ty, amount))
        });
    }

    #[test]
    fn shr_1() {
        test_gate([1, 2], |c, [a, b]| {
            let amount = eval::eval_wire_secret(c, b).unwrap().unwrap_single().unwrap();
            c.shr(a, c.lit(b.ty, amount))
        });
        test_gate([-1, 2], |c, [a, b]| {
            let amount = eval::eval_wire_secret(c, b).unwrap().unwrap_single().unwrap();
            c.shr(a, c.lit(b.ty, amount))
        });
    }


    #[test]
    fn neg_1() {
        test_gate([1], |c, [w]| c.neg(w));
    }

    #[test]
    fn add_1() {
        test_gate([1, 1], |c, [a, b]| c.add(a, b));
    }

    #[test]
    fn sub_1() {
        test_gate([1, 1], |c, [a, b]| c.sub(a, b));
    }

    #[test]
    fn mul_1() {
        test_gate([1, 1], |c, [a, b]| c.mul(a, b));
    }

    #[test]
    fn wide_mul_1() {
        test_gate([1, 1], |c, [a, b]| {
            let gk = c.intern_gadget_kind(WideMul);
            c.gadget(gk, &[a, b])
        });
    }

    #[test]
    fn div_1() {
        test_gate([1, 1], |c, [a, b]| c.div(a, b));
    }

    #[test]
    fn mod_1() {
        test_gate([1, 1], |c, [a, b]| c.mod_(a, b));
    }


    #[test]
    fn eq_1() {
        test_gate([1, 1], |c, [a, b]| c.eq(a, b));
        test_gate([-1, -1], |c, [a, b]| c.eq(a, b));
        test_gate([1], |c, [a]| c.eq(a, c.lit(a.ty, 0)));
        test_gate([-1], |c, [a]| c.eq(a, c.lit(a.ty, 0)));
    }

    #[test]
    fn ne_1() {
        test_gate([1, 1], |c, [a, b]| c.ne(a, b));
        test_gate([-1, -1], |c, [a, b]| c.ne(a, b));
        test_gate([1], |c, [a]| c.ne(a, c.lit(a.ty, 0)));
        test_gate([-1], |c, [a]| c.ne(a, c.lit(a.ty, 0)));
    }

    #[test]
    fn lt_1() {
        test_gate([1], |c, [a]| c.lt(a, c.lit(a.ty, 0)));
        test_gate([-1], |c, [a]| c.lt(a, c.lit(a.ty, 0)));
    }

    #[test]
    fn gt_1() {
        test_gate([1], |c, [a]| c.gt(a, c.lit(a.ty, 0)));
        test_gate([-1], |c, [a]| c.gt(a, c.lit(a.ty, 0)));
    }

    #[test]
    fn le_1() {
        test_gate([1], |c, [a]| c.le(a, c.lit(a.ty, 0)));
        test_gate([-1], |c, [a]| c.le(a, c.lit(a.ty, 0)));
    }

    #[test]
    fn ge_1() {
        test_gate([1], |c, [a]| c.ge(a, c.lit(a.ty, 0)));
        test_gate([-1], |c, [a]| c.ge(a, c.lit(a.ty, 0)));
    }


    #[test]
    fn mux_1() {
        // Skip SIEVE IR v2 evaluation, since the current evaluator doesn't support the `mux_v0`
        // plugin we use.
        test_gate_skip_v2_eval([1, 1, 1], |c, [x, y, z]| c.mux(x, y, z));
        test_gate_skip_v2_eval([1, -1, -1], |c, [x, y, z]| c.mux(x, y, z));
    }


    #[test]
    fn not_3() {
        test_gate([3], |c, [w]| c.not(w));
    }

    #[test]
    fn and_3() {
        test_gate([3, 3], |c, [a, b]| c.and(a, b));
    }

    #[test]
    fn or_3() {
        test_gate([3, 3], |c, [a, b]| c.or(a, b));
    }

    #[test]
    fn xor_3() {
        test_gate([3, 3], |c, [a, b]| c.xor(a, b));
    }

    #[test]
    fn shl_3() {
        test_gate([3, 3], |c, [a, b]| {
            let amount = eval::eval_wire_secret(c, b).unwrap().unwrap_single().unwrap();
            c.shl(a, c.lit(b.ty, amount))
        });
        test_gate([-3, 3], |c, [a, b]| {
            let amount = eval::eval_wire_secret(c, b).unwrap().unwrap_single().unwrap();
            c.shl(a, c.lit(b.ty, amount))
        });
    }

    #[test]
    fn shr_3() {
        test_gate([3, 3], |c, [a, b]| {
            let amount = eval::eval_wire_secret(c, b).unwrap().unwrap_single().unwrap();
            c.shr(a, c.lit(b.ty, amount))
        });
        test_gate([-3, 3], |c, [a, b]| {
            let amount = eval::eval_wire_secret(c, b).unwrap().unwrap_single().unwrap();
            c.shr(a, c.lit(b.ty, amount))
        });
    }


    #[test]
    fn neg_3() {
        test_gate([3], |c, [w]| c.neg(w));
    }

    #[test]
    fn add_3() {
        test_gate([3, 3], |c, [a, b]| c.add(a, b));
    }

    #[test]
    fn sub_3() {
        test_gate([3, 3], |c, [a, b]| c.sub(a, b));
    }

    #[test]
    fn mul_3() {
        test_gate([3, 3], |c, [a, b]| c.mul(a, b));
    }

    #[test]
    fn wide_mul_3() {
        test_gate([3, 3], |c, [a, b]| {
            let gk = c.intern_gadget_kind(WideMul);
            c.gadget(gk, &[a, b])
        });
    }

    #[test]
    fn div_3() {
        test_gate([3, 3], |c, [a, b]| c.div(a, b));
    }

    #[test]
    fn mod_3() {
        test_gate([3, 3], |c, [a, b]| c.mod_(a, b));
    }


    #[test]
    fn eq_3() {
        test_gate([3, 3], |c, [a, b]| c.eq(a, b));
        test_gate([-3, -3], |c, [a, b]| c.eq(a, b));
        test_gate([3], |c, [a]| c.eq(a, c.lit(a.ty, 0)));
        test_gate([-3], |c, [a]| c.eq(a, c.lit(a.ty, 0)));
    }

    #[test]
    fn ne_3() {
        test_gate([3, 3], |c, [a, b]| c.ne(a, b));
        test_gate([-3, -3], |c, [a, b]| c.ne(a, b));
        test_gate([3], |c, [a]| c.ne(a, c.lit(a.ty, 0)));
        test_gate([-3], |c, [a]| c.ne(a, c.lit(a.ty, 0)));
    }

    #[test]
    fn lt_3() {
        test_gate([3], |c, [a]| c.lt(a, c.lit(a.ty, 0)));
        test_gate([-3], |c, [a]| c.lt(a, c.lit(a.ty, 0)));
    }

    #[test]
    fn gt_3() {
        test_gate([3], |c, [a]| c.gt(a, c.lit(a.ty, 0)));
        test_gate([-3], |c, [a]| c.gt(a, c.lit(a.ty, 0)));
    }

    #[test]
    fn le_3() {
        test_gate([3], |c, [a]| c.le(a, c.lit(a.ty, 0)));
        test_gate([-3], |c, [a]| c.le(a, c.lit(a.ty, 0)));
    }

    #[test]
    fn ge_3() {
        test_gate([3], |c, [a]| c.ge(a, c.lit(a.ty, 0)));
        test_gate([-3], |c, [a]| c.ge(a, c.lit(a.ty, 0)));
    }


    #[test]
    fn mux_3() {
        // Skip SIEVE IR v2 evaluation, since the current evaluator doesn't support the `mux_v0`
        // plugin we use.
        test_gate_skip_v2_eval([1, 3, 3], |c, [x, y, z]| c.mux(x, y, z));
        test_gate_skip_v2_eval([1, -3, -3], |c, [x, y, z]| c.mux(x, y, z));
    }
}
