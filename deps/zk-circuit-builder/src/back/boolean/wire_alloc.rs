use std::cmp::{self, Ordering};
use std::collections::BinaryHeap;
use std::iter;
use std::mem;
use super::{Time, WireId};


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
pub struct WireAlloc {
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

    pub fn preallocate<const N: usize>(&mut self, ns: [u64; N]) -> [WireId; N] {
        let bucket = &mut self.buckets[0];
        // We require that no normal allocations have been performed yet.
        assert_eq!(bucket.next, bucket.page_start);

        let mut next = bucket.next;
        let mut ws = [0; N];
        for (&n, w) in ns.iter().zip(ws.iter_mut()) {
            *w = next;
            next += n;
        }
        let end = bucket.end;

        *bucket = WireBucket::new(next, end);

        ws
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
pub struct AllocPage {
    pub pos: usize,
    pub start: WireId,
    pub end: WireId,
}

/// Indicates that the page `start .. end` should be freed at time `expire`.
pub struct FreePage {
    pub expire: Time,
    pub start: WireId,
    pub end: WireId,
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
