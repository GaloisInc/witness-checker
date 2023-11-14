use crate::{
    eval::{self, CachingEvaluator},
    ir::{
        circuit::{Bits, CircuitTrait, Ty},
        typed::{
            self, Builder, BuilderExt, EvaluatorExt, FromEval, FromWireList, LazySecret, Le, Lit,
            Mux, Repr, SecretDep, TWire, ToWireList,
        },
    },
    routing::sort::{sort_by_key, CompareLe},
};

use crate::ir::circuit::Wire;

/// A ROM entry with an address and a value.
#[derive(Clone)]
pub struct ROMPort<T> {
    pub addr: u64,
    pub val: T,
}

pub struct ROMPortRepr<'a, T: Repr<'a>> {
    pub addr: TWire<'a, u64>,
    pub val: TWire<'a, T>,
}

impl<'a, T: Repr<'a>> Copy for ROMPortRepr<'a, T> where <T as Repr<'a>>::Repr: Copy {}

impl<'a, T: Repr<'a>> Clone for ROMPortRepr<'a, T>
where
    <T as Repr<'a>>::Repr: Copy,
{
    fn clone(&self) -> Self {
        ROMPortRepr {
            addr: self.addr,
            val: self.val,
        }
    }
}

impl<'a, T: Repr<'a>> Repr<'a> for ROMPort<T> {
    type Repr = ROMPortRepr<'a, T>;
}

impl<'a, T> Le<'a> for ROMPort<T>
where
    T: Repr<'a>,
{
    type Output = bool;

    fn le(
        bld: &impl Builder<'a>,
        a: ROMPortRepr<'a, T>,
        b: ROMPortRepr<'a, T>,
    ) -> <Self::Output as Repr<'a>>::Repr {
        *bld.le(a.addr, b.addr)
    }
}

impl<'a, T> ToWireList<'a> for ROMPort<T>
where
    T: Repr<'a>,
    T: ToWireList<'a>,
{
    fn num_wires(x: &Self::Repr) -> usize {
        u64::num_wires(&x.addr.repr) + T::num_wires(&x.val.repr)
    }
    fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
        u64::for_each_wire(&x.addr.repr, |w| f(w));
        T::for_each_wire(&x.val.repr, |w| f(w));
    }
    fn num_sizes(x: &Self::Repr) -> usize {
        u64::num_sizes(&x.addr.repr) + T::num_sizes(&x.val.repr)
    }
    fn for_each_size(x: &Self::Repr, mut f: impl FnMut(usize)) {
        u64::for_each_size(&x.addr.repr, |w| f(w));
        T::for_each_size(&x.val.repr, |w| f(w));
    }
}

impl<'a, C: Repr<'a>, T> Mux<'a, C, ROMPort<T>> for ROMPort<T>
where
    T: Repr<'a>,
    C::Repr: Clone,
    u64: Mux<'a, C, u64, Output = u64>,
    T: Mux<'a, C, T, Output = T>,
{
    type Output = ROMPort<T>;

    fn mux(
        bld: &impl Builder<'a>,
        c: C::Repr,
        t: ROMPortRepr<'a, T>,
        e: ROMPortRepr<'a, T>,
    ) -> ROMPortRepr<'a, T> {
        let c: TWire<C> = TWire::new(c);
        ROMPortRepr {
            addr: bld.mux(c.clone(), t.addr, e.addr),
            val: bld.mux(c, t.val, e.val),
        }
    }
}

impl<'a, T> FromWireList<'a> for ROMPort<T>
where
    T: Repr<'a>,
    T: FromWireList<'a>,
{
    fn expected_num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize {
        u64::expected_num_wires(sizes) + T::expected_num_wires(sizes)
    }

    fn for_each_expected_wire_type<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        sizes: &mut impl Iterator<Item = usize>,
        mut f: impl FnMut(Ty<'a>),
    ) {
        u64::for_each_expected_wire_type(c, sizes, |w| f(w));
        T::for_each_expected_wire_type(c, sizes, |w| f(w));
    }

    fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        sizes: &mut impl Iterator<Item = usize>,
        build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
    ) -> Self::Repr {
        let addr = TWire::new(u64::build_repr_from_wires(c, sizes, build_wire));
        let val = TWire::new(T::build_repr_from_wires(c, sizes, build_wire));
        ROMPortRepr { addr, val }
    }
}
impl<'a, T> SecretDep<'a> for ROMPort<T>
where
    T: Repr<'a>,
    T: SecretDep<'a, Decoded = T>,
{
    type Decoded = ROMPort<T>;
    fn from_bits_iter(
        sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> Self {
        ROMPort {
            addr: u64::from_bits_iter(sizes, bits),
            val: T::from_bits_iter(sizes, bits),
        }
    }
}

impl<'a, T> LazySecret<'a> for ROMPort<T>
where
    T: Repr<'a> + LazySecret<'a>,
{
    fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
        u64::expected_word_len(sizes) + T::expected_word_len(sizes)
    }
    fn word_len(&self) -> usize {
        u64::word_len(&self.addr) + T::word_len(&self.val)
    }
    fn push_words(&self, out: &mut Vec<u32>) {
        u64::push_words(&self.addr, out);
        T::push_words(&self.val, out);
    }
}

/// A struct representing a read-only memory whose access is verified in the circuit.
pub struct ROM<'a, T>
where
    T: Repr<'a>,
{
    ports: Vec<TWire<'a, ROMPort<T>>>,
    sizes: Vec<usize>,
    length: u64,
}

impl<'a, T: Repr<'a> + Lit<'a>> Lit<'a> for ROMPort<T> {
    fn lit(bld: &impl Builder<'a>, a: Self) -> Self::Repr {
        ROMPortRepr {
            addr: bld.lit(a.addr),
            val: bld.lit(a.val),
        }
    }
}

impl<'a, T> ROM<'a, T>
where
    T: Clone,
    T: for<'b> LazySecret<'b>,
    <T as Repr<'a>>::Repr: Copy,
    T: for<'b> SecretDep<'b, Decoded = T>,
{
    /// Reads a wire value from ROM at the given `index`. Make sure to call `finalize` after all `load` calls. `index` must be in bounds, otherwise `finalize` will fail. 
    pub fn load(&mut self, b: &impl Builder<'a>, index: TWire<'a, u64>) -> TWire<'a, T> {
        let ports: TWire<'a, Vec<ROMPort<T>>> = TWire::new(self.ports.clone());
        let inp: TWire<(u64, Vec<ROMPort<T>>)> = TWire::new((index, ports));
        // JP: Should this be `secret_derived`?
        let val: TWire<'a, T> = b.secret_derived_sized(&self.sizes, inp, move |(i, ps)| {
            ps[i as usize].val.clone()
        });

        // create a new rom port
        let port = TWire::new(ROMPortRepr { addr: index, val });
        // add it to the vec
        self.ports.push(port);
        val
    }
}

impl<'a, T> ROM<'a, T>
where
    T: Clone,
    T: typed::Eq<'a, Output = bool>,
    <T as Repr<'a>>::Repr: Copy,
    T: Mux<'a, bool, T, Output = T>,
    T: ToWireList<'a>,
    T: FromWireList<'a>,
{
    /// Create a `ROM` (read only memory) to obliviously read values from the provided `values` list.
    pub fn new(b: &impl Builder<'a>, values: Vec<TWire<'a, T>>) -> ROM<'a, T> {
        let length = values.len() as u64;
        let mut sizes = Vec::new();

        let ports = values
            .into_iter()
            .enumerate()
            .map(|(i, v)| {
                let size = T::num_sizes(&v.repr);
                sizes.push(size);

                TWire::new(ROMPortRepr {
                    addr: b.lit(i as u64),
                    val: v,
                })
            })
            .collect();

        ROM { ports, length, sizes }
    }

    /// Performs all necessary checks in the circuit to validate that all ROM reads are correctly executed via `load`. The caller is responsible for asserting that the returned boolean wire is `true`.
    pub fn finalize(self, b: &'a impl Builder<'a>) -> TWire<bool> {
        // Create secrets for sorted ROMPorts
        // If prover, sort ROMPorts and set corresponding secrets

        // Step 1: Sort Memory Accesses
        // Instead of handling memory accesses in the order they're executed,
        // the circuit first sorts all memory accesses by address.
        let sort = sort_by_key(b, &self.ports, CompareLe, |p| p.repr.addr);

        // JP: Do we need Rooted things?
        // In circuit, check that the secrets are sorted
        let (sorted_ports, is_sorted) = sort.finish(b);

        let mut res = is_sorted;

        // Step 2: Validate Memory Accesses
        // To ensure that the computations are consistent with RAM,
        // we verify in circuit the validity of the sorted memory accesses:
        // If two subsequent accesses have the same address, they must also
        // have the same value.
        for i in 1..sorted_ports.len() {
            let port0 = sorted_ports[i - 1];
            let port1 = sorted_ports[i];
            let addr_eq = b.eq(port0.addr, port1.addr);
            let val_eq: TWire<bool> = b.eq(port0.val, port1.val);
            res = b.and(res, b.mux(addr_eq, val_eq, b.lit(true)));
        }

        // Step 3: Check highest address
        // All addresses are expected to be numbered from 0 to n-1.
        // This guarantees that the final address in the sorted values equals n-1
        // and that no read operations were out-of-bounds.
        if self.length > 0 {
            let is_final_address = b.eq(
                sorted_ports[sorted_ports.len() - 1].addr,
                b.lit(self.length - 1),
            );

            res = b.and(res, is_final_address);
        }
        res
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::circuit::{Arenas, Circuit, FilterNil};
    use crate::ir::typed::BuilderImpl;

    pub struct Context<'a, 's> {
        eval: CachingEvaluator<'a, 's, eval::RevealSecrets>,
    }
    
    impl<'a, 's> Context<'a, 's> {
        pub fn new<C: CircuitTrait<'a> + ?Sized>(_c: &'a C) -> Context<'a, 's> {
            Context {
                eval: CachingEvaluator::new(),
            }
        }
        pub fn reveal<T: Repr<'a> + FromEval<'a> + Default, C: CircuitTrait<'a> + ?Sized>(
            &mut self,
            c: &'a C,
            secret: TWire<'a, T>,
            _b: &impl Builder<'a>,
        ) -> T {
            let res_plaintext = self.eval.eval_typed(c, secret);
            match res_plaintext {
                None => T::default(),
                Some(b) => b,
            }
        }
    }

    #[test]
    fn test_rom() {
        let arenas = Arenas::new();
        let c = Circuit::new::<u32>(&arenas, true, FilterNil);
        let builder = BuilderImpl::from_ref(&c);
        let mut ctx = Context::new(&c);

        let values = vec![builder.lit(10), builder.lit(20), builder.lit(30)];

        // test_rom_initialization
        let mut rom = ROM::new(builder, values.clone());
        assert_eq!(rom.length as usize, values.len());

        // test_rom_load
        let initial_len = rom.ports.len();
        let port_val = rom.load(builder, builder.lit(1));
        assert_eq!(ctx.reveal(&c, port_val, builder), 20);
        assert_eq!(rom.ports.len(), initial_len + 1);

        // test_rom_finalize
        let result = rom.finalize(builder);
        assert!(ctx.reveal(&c, result, builder));
    }

    #[test]
    #[should_panic(expected = "index out of bounds")]
    fn test_out_of_bounds_rom() {
        let arenas = Arenas::new();
        let c = Circuit::new::<u32>(&arenas, true, FilterNil);
        let builder = BuilderImpl::from_ref(&c);
        let mut ctx = Context::new(&c);

        let values = vec![builder.lit(10), builder.lit(20), builder.lit(30)];

        let mut rom = ROM::new(builder, values.clone());
        rom.load(builder, builder.lit(3)); // 3 is out of bounds
        let result = rom.finalize(builder);
        assert!(ctx.reveal(&c, result, builder));
    }
}
