use crate::ir::typed::{Builder, TWire, Repr, Mux};

// An implementation of Batcher odd-even mergesort, as described on Wikipedia:
// https://en.wikipedia.org/wiki/Batcher_odd%E2%80%93even_mergesort
// Extended for non-power-of-two lengths:
// https://stackoverflow.com/a/34025537

struct MergeSort<'a, 'b, T: Repr<'a>, F> {
    b: &'b Builder<'a>,
    xs: &'b mut [TWire<'a, T>],
    compare: &'b mut F,
}

impl<'a, 'b, T, F> MergeSort<'a, 'b, T, F>
where
    T: Mux<'a, bool, T, Output = T>,
    T::Repr: Clone,
    F: FnMut(&TWire<'a, T>, &TWire<'a, T>) -> TWire<'a, bool>,
{
    fn merge(&mut self, lo: usize, hi: usize) {
        let mut q = (hi - lo + 1).next_power_of_two() / 2;
        let mut r = 0;
        let mut d = 1;

        while d > 0 {
            for i in lo .. hi - d {
                if i & 1 == r {
                    self.maybe_swap(i, i + d);
                }
            }
            d = q - 1;
            q /= 2;
            r = 1;
        }
    }

    /// Sort the elements of `self.xs` between `lo` and `hi` (inclusive).
    fn sort_range(&mut self, lo: usize, hi: usize) {
        if hi - lo >= 1 {
            let mid = lo + (hi - lo) / 2;
            self.sort_range(lo, mid);
            self.sort_range(mid + 1, hi);
            self.merge(lo, hi);
        }
    }

    fn sort(&mut self) {
        let len = self.xs.len();
        self.sort_range(0, len - 1);
    }

    fn maybe_swap(&mut self, i: usize, j: usize) {
        assert!(i < j);
        let a = &self.xs[i];
        let b = &self.xs[j];
        let lt = (self.compare)(a, b);
        let new_a = self.b.mux(lt, a.clone(), b.clone());
        let new_b = self.b.mux(lt, b.clone(), a.clone());
        self.xs[i] = new_a;
        self.xs[j] = new_b;
    }
}

/// Sort `xs` in-place.  `compare(a, b)` should return `true` when `a` is less than `b`.
///
/// This is an unstable sort.
pub fn sort<'a, T, F>(b: &Builder<'a>, xs: &mut [TWire<'a, T>], compare: &mut F)
where
    T: Mux<'a, bool, T, Output = T>,
    T::Repr: Clone,
    F: FnMut(&TWire<'a, T>, &TWire<'a, T>) -> TWire<'a, bool>,
{
    MergeSort { b, xs, compare }.sort();
}
