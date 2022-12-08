use std::cmp::{self, Ordering};
use std::collections::BinaryHeap;
use std::convert::TryFrom;
use std::iter;
use std::mem;
use crate::ir::circuit::Bits;
use zki_sieve_v3::{self, Gate};
use super::{Sink, WireId, Time, TEMP, Source};
use super::arith;


pub struct SieveIrV2Sink<S> {
    sink: S,
    alloc: WireAlloc,
    gates: Vec<Gate>,
    private_bits: Vec<bool>,
    /// Whether we've emitted a relation message yet.  The first relation message must contain some
    /// additional data.
    emitted_relation: bool,
}

const GATE_PAGE_SIZE: usize = 64 * 1024;

impl<S: zki_sieve_v3::Sink> SieveIrV2Sink<S> {
    pub fn new(sink: S) -> SieveIrV2Sink<S> {
        SieveIrV2Sink {
            sink,
            alloc: WireAlloc::new(vec![
                0,          // 0 (temporaries)
                1 << 4,     // 16
                1 << 6,     // 64
                1 << 8,     // 256
                1 << 11,    // 2k
                1 << 14,    // 16k
                1 << 18,    // 256k
            ]),
            gates: Vec::new(),
            private_bits: Vec::new(),
            emitted_relation: false,
        }
    }

    pub fn finish(mut self) -> S {
        self.flush(true);
        self.sink
    }

    fn alloc_wires(&mut self, expire: Time, n: u64) -> WireId {
        self.alloc.alloc(expire, n, self.gates.len())
    }

    fn flush(&mut self, free_all_pages: bool) {
        use zki_sieve_v3::Sink;
        use zki_sieve_v3::structs::IR_VERSION;
        use zki_sieve_v3::structs::directives::Directive;
        use zki_sieve_v3::structs::private_inputs::PrivateInputs;
        use zki_sieve_v3::structs::relation::Relation;
        use zki_sieve_v3::structs::types::Type;

        let allocs = self.alloc.flush();

        if free_all_pages {
            for free in self.alloc.take_frees() {
                if free.start != free.end {
                    self.gates.push(Gate::Delete(0, free.start, free.end - 1));
                }
            }
        }

        let mut directives = Vec::with_capacity(self.gates.len() + allocs.len());
        let mut iter = mem::take(&mut self.gates).into_iter();
        let mut prev = 0;
        for alloc in allocs {
            let n = alloc.pos - prev;
            directives.extend(iter.by_ref().take(n).map(|g| Directive::Gate(g)));
            prev = alloc.pos;

            if alloc.start != alloc.end {
                directives.push(Directive::Gate(Gate::New(0, alloc.start, alloc.end - 1)));
            }
        }
        directives.extend(iter.map(|g| Directive::Gate(g)));

        // Build and emit the messages
        let mut r = Relation {
            version: IR_VERSION.to_string(),
            plugins: Vec::new(),
            types: Vec::new(),
            conversions: Vec::new(),
            directives,
        };
        if !self.emitted_relation {
            r.types = vec![Type::Field(vec![2])];
        }
        self.sink.push_relation_message(&r).unwrap();
        self.emitted_relation = true;

        let inputs = mem::take(&mut self.private_bits).into_iter()
            .map(|b| vec![b as u8]).collect();
        let mut p = PrivateInputs {
            version: IR_VERSION.to_string(),
            type_value: Type::Field(vec![2]),
            inputs,
        };
        self.sink.push_private_inputs_message(&p).unwrap();
    }

    fn lit_zero_into(&mut self, out: WireId, n: u64) {
        for i in 0 .. n {
            self.gates.push(Gate::Constant(0, out + i, vec![0]));
        }
    }

    fn lit_one_into(&mut self, out: WireId, n: u64) {
        for i in 0 .. n {
            self.gates.push(Gate::Constant(0, out + i, vec![1]));
        }
    }

    fn copy_into(&mut self, out: WireId, n: u64, a: WireId) {
        for i in 0 .. n {
            self.gates.push(Gate::Copy(0, out + i, a + i));
        }
    }
}

impl<S: zki_sieve_v3::Sink> Sink for SieveIrV2Sink<S> {
    fn lit(&mut self, expire: Time, n: u64, bits: Bits) -> WireId {
        let w = self.alloc_wires(expire, n);
        for i in 0 .. n {
            let bit = bits.get(i as usize);
            self.gates.push(Gate::Constant(0, w + i, vec![bit as u8]));
        }
        w
    }
    fn private(&mut self, expire: Time, n: u64, value: Option<Bits>) -> WireId {
        let w = self.alloc_wires(expire, n);
        for i in 0 .. n {
            self.gates.push(Gate::Private(0, w + i));
            if let Some(v) = value.as_ref() {
                self.private_bits.push(v.get(i as usize));
            }
        }
        w
    }
    fn copy(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
        let w = self.alloc_wires(expire, n);
        self.copy_into(w, n, a);
        w
    }
    fn concat_chunks(&mut self, expire: Time, entries: &[(Source, u64)]) -> WireId {
        let total = entries.iter().map(|&(_, n)| n).sum();
        let w = self.alloc_wires(expire, total);
        let mut pos = 0;
        for &(source, n) in entries {
            match source {
                Source::Zero => {
                    self.lit_zero_into(w + pos, n);
                },
                Source::One => {
                    self.lit_one_into(w + pos, n);
                },
                Source::Wires(a) => {
                    self.copy_into(w + pos, n, a);
                },
                Source::RepWire(a) => {
                    for i in 0 .. n {
                        self.gates.push(Gate::Copy(0, w + pos + i, a));
                    }
                },
            }
            pos += n;
        }
        w
    }

    fn and(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        let w = self.alloc_wires(expire, n);
        for i in 0 .. n {
            self.gates.push(Gate::Mul(0, w + i, a + i, b + i));
        }
        w
    }
    fn or(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        let a_inv = self.not(TEMP, n, a);
        let b_inv = self.not(TEMP, n, b);
        let ab_inv = self.and(TEMP, n, a_inv, b_inv);
        self.not(expire, n, ab_inv)
    }
    fn xor(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        let w = self.alloc_wires(expire, n);
        for i in 0 .. n {
            self.gates.push(Gate::Add(0, w + i, a + i, b + i));
        }
        w
    }
    fn not(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
        let w = self.alloc_wires(expire, n);
        for i in 0 .. n {
            self.gates.push(Gate::AddConstant(0, w + i, a + i, vec![1]));
        }
        w
    }

    fn add(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        arith::add(self, expire, n, a, b)
    }
    fn sub(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        arith::sub(self, expire, n, a, b)
    }
    fn mul(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        arith::mul(self, expire, n, a, b)
    }
    fn wide_mul(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        arith::wide_mul(self, expire, n, a, b)
    }
    fn neg(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
        arith::neg(self, expire, n, a)
    }

    fn assert_zero(&mut self, n: u64, a: WireId) {
        for i in 0 .. n {
            self.gates.push(Gate::AssertZero(0, a + i));
        }
    }

    fn free_expired(&mut self, now: Time) {
        for free in self.alloc.advance(now) {
            if free.start != free.end {
                self.gates.push(Gate::Delete(0, free.start, free.end - 1));
            }
        }

        if self.gates.len() >= GATE_PAGE_SIZE {
            self.flush(false);
        }
    }
}


/// # Page lifecycle
///
/// Each bucket has a current page.  Allocating from the bucket will allocate some wires within the
/// current page; if there isn't enough space in this page, it will finish the current page and
/// start a new one.  Calling `flush` forcibly finishes the current page and starts a new one.
///
/// One major problem we have to deal with here is that the alloc operation must know exactly how
/// many wires will be initialized within the page.  Every wire must be initialized before the page
/// can be freed, so allocating excess wires mean we must waste gates initializing those wires when
/// it comes time to free the page.  To handle this, instead of emitting the alloc operation when
/// the page is created, we record the current position in the output buffer; later, when the page
/// is finished and the number of initialized wires is known, we emit an `AllocPage` record
/// describing an alloc operation that should be inserted at a particular place in the gate stream
/// when the final output buffer is built.
///
/// When a page is finished, two things happen.  First, we emit an `AllocPage` that indicates where
/// the page's `Alloc` gate should be inserted in the output stream.  Second, we emit a `FreePage`
/// to schedule insertion of the page's `Free` gate at some point in the future.
struct WireAlloc {
    bucket_lifespans: Vec<u32>,
    buckets: Vec<WireBucket>,
    /// List of allocs to be inserted into the output stream.  An entry `(i, gate)` means that
    /// `gate` should be inserted before gate `i` of the main output buffer.
    allocs: Vec<AllocPage>,
    /// List of pages to be freed at various times in the future.
    frees: BinaryHeap<FreePage>,
    now: Time,
}

impl WireAlloc {
    pub fn new(mut bucket_lifespans: Vec<u32>) -> WireAlloc {
        bucket_lifespans.sort();

        let mut buckets = Vec::with_capacity(bucket_lifespans.len() + 1);
        let step = WireId::MAX / (bucket_lifespans.len() as u64 + 1);
        for i in 0 .. bucket_lifespans.len() + 1 {
            let start = step * (i as u64);
            let end = step * (i as u64 + 1);
            buckets.push(WireBucket::new(start, end));
        }

        WireAlloc {
            bucket_lifespans,
            buckets,
            allocs: Vec::new(),
            frees: BinaryHeap::new(),
            now: 0,
        }
    }

    pub fn alloc(
        &mut self,
        expire: Time,
        n: u64,
        next_alloc_pos: usize,
    ) -> WireId {
        let lifespan = expire.saturating_sub(self.now);
        let i = self.bucket_lifespans.iter().cloned().position(|bl| lifespan <= bl as Time)
            .unwrap_or(self.bucket_lifespans.len());
        let (wire, opt_page) = self.buckets[i].alloc(expire, n, next_alloc_pos);
        if let Some((alloc, free)) = opt_page {
            self.allocs.push(alloc);
            self.frees.push(free);
        }
        wire
    }

    /// Close all open pages and start a new output chunk.  Returns a list of allocations to
    /// insert in the output, sorted by insertion position.
    pub fn flush(&mut self) -> Vec<AllocPage> {
        let mut allocs = mem::take(&mut self.allocs);
        for bucket in &mut self.buckets {
            let (alloc, free) = bucket.flush(0);
            allocs.push(alloc);
            self.frees.push(free);
        }
        allocs.sort_by_key(|a| a.pos);
        allocs
    }

    /// Set the current time to `now`.  Returns an iterator over pages that should now be freed,
    /// due to expiring before the new current time.
    pub fn advance<'a>(&'a mut self, now: Time) -> impl Iterator<Item = FreePage> + 'a {
        self.now = now;
        let frees = &mut self.frees;
        iter::from_fn(move || {
            if frees.peek()?.expire <= now {
                frees.pop()
            } else {
                None
            }
        })
    }

    pub fn take_frees<'a>(&'a mut self) -> impl Iterator<Item = FreePage> + 'a {
        mem::take(&mut self.frees).into_iter()
    }
}

struct WireBucket {
    next: WireId,
    end: WireId,
    /// The expiration time of the last gate in the current page.
    expire: Time,
    page_start: WireId,
    page_end: WireId,
    /// The position where the alloc gate should be inserted within the main output buffer.
    alloc_pos: usize,
}

const PAGE_SIZE: u64 = 4096;

impl WireBucket {
    pub fn new(start: WireId, end: WireId) -> WireBucket {
        let page_start = start;
        let page_end = page_start + cmp::min(end - start, PAGE_SIZE);
        WireBucket {
            next: start,
            end,
            expire: 0,
            page_start,
            page_end,
            alloc_pos: 0,
        }
    }

    pub fn alloc(
        &mut self,
        expire: Time,
        n: u64,
        next_alloc_pos: usize,
    ) -> (WireId, Option<(AllocPage, FreePage)>) {
        self.expire = cmp::max(self.expire, expire);

        if n <= self.page_end - self.next {
            let w = self.next;
            self.next += n;
            return (w, None);
        }

        let (alloc, free) = self.flush(next_alloc_pos);
        if n <= PAGE_SIZE {
            let w = self.next;
            self.next += n;
            return (w, Some((alloc, free)));
        }

        // `n > PAGE_SIZE`.  Try to extend the new page to length `n`.
        assert!(n <= self.end - self.next);
        debug_assert!(self.next == self.page_start);
        self.page_end = self.page_start + n;

        let w = self.next;
        self.next += n;
        return (w, Some((alloc, free)));
    }

    pub fn flush(&mut self, next_alloc_pos: usize) -> (AllocPage, FreePage) {
        let alloc = AllocPage {
            pos: self.alloc_pos,
            start: self.page_start,
            end: self.next,
        };
        let free = FreePage {
            expire: self.expire,
            start: self.page_start,
            end: self.next,
        };
        assert!(self.next < self.end);
        self.page_start = self.next;
        self.page_end = self.page_start + cmp::min(self.end - self.next, PAGE_SIZE);
        self.expire = 0;
        self.alloc_pos = next_alloc_pos;
        (alloc, free)
    }
}

/// Indicates that the page `start .. end` should be allocated before gate `i` of the main output
/// buffer.
struct AllocPage {
    pos: usize,
    start: WireId,
    end: WireId,
}

/// Indicates that the page `start .. end` should be freed at time `expire`.
struct FreePage {
    expire: Time,
    start: WireId,
    end: WireId,
}

impl PartialEq for FreePage {
    fn eq(&self, other: &FreePage) -> bool {
        self.expire == other.expire
    }
}

impl Eq for FreePage {}

impl PartialOrd for FreePage {
    fn partial_cmp(&self, other: &FreePage) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for FreePage {
    fn cmp(&self, other: &FreePage) -> Ordering {
        self.expire.cmp(&other.expire).reverse()
    }
}
