use crate::ir::typed::{Builder, TWire, Repr, Mux};

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

    /// Batcher's odd-even mergesort:
    /// https://www.inf.hs-flensburg.de/lang/algorithmen/sortieren/networks/oemen.htm
    ///
    /// This algorithm works only for arrays of power-of-two length.  To extend it to
    /// non-power-of-two sizes, we imagine padding the array with enough infinities to extend it to
    /// the next larger power of two.  Since we already know the infinities come after all real
    /// array elements, we don't need to emit comparisons between real values and infinities.
    fn sort(&mut self) {
        if self.xs.len() <= 1 {
            return;
        }
        self.sort_range(0, self.xs.len().next_power_of_two());
    }

    fn sort_range(&mut self, lo: usize, hi: usize) {
        let len = hi - lo;
        assert!(len >= 2);
        if len == 2 {
            self.maybe_swap(lo, lo + 1);
        } else {
            let mid = lo + len / 2;
            self.sort_range(lo, mid);
            self.sort_range(mid, hi);
            self.merge(lo, hi, 1);
        }
    }

    /// Sort the sequence `xs[lo], xs[lo + step], xs[lo + 2 * step], ..., xs[hi - step]`.
    fn merge(&mut self, lo: usize, hi: usize, step: usize) {
        let len = (hi - lo) / step;
        assert!(len >= 2);
        if len == 2 {
            self.maybe_swap(lo, lo + step);
            return;
        }

        self.merge(lo, hi, step * 2);
        self.merge(lo + step, hi + step, step * 2);

        for i in (lo + step .. hi - step).step_by(step * 2) {
            self.maybe_swap(i, i + step);
        }
    }

    fn maybe_swap(&mut self, i: usize, j: usize) {
        assert!(i < j);
        if j >= self.xs.len() {
            // No need to swap.  `xs[j]` is a virtual infinity, guaranteed to be larger than
            // `xs[i]` (unless both are infinity, in which case there's no need to swap).
            return;
        }

        let a = &self.xs[i];
        let b = &self.xs[j];
        let lt = (self.compare)(a, b);
        let _g = self.b.scoped_label("swap");
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
