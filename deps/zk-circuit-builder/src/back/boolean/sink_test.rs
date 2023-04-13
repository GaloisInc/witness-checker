use std::collections::{HashMap, BTreeMap};
use log::*;
use num_bigint::BigUint;
use num_traits::Zero;
use crate::back::boolean::{Sink, WireId, Source, Time};
use crate::ir::circuit::Bits;


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
        self.init(expire, n, |_, i| <BigUint>::bit(&out_uint, i),
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
