use crate::{
    ir::{
        circuit::{Bits, CircuitTrait, Ty},
        typed::{
            self, Builder, BuilderExt, FromWireList, LazySecret, Le, Lit, Mux, Repr, SecretDep,
            TWire, ToWireList,
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

impl<'a, T: Repr<'a>> ROM<'a, T> {
    pub fn new(_b: &impl Builder<'a>, _values: &[TWire<'a, T>]) -> ROM<'a, T> {
        ROM {
            phantom: PhantomData,
        }
    }
}

    pub fn load(&mut self, _b: &impl Builder<'a>, _index: TWire<'a, u64>) -> TWire<'a, T> {
        unimplemented!{}
    }

    pub fn assert_consistent(self, _b: &impl Builder<'a>) {
    // mh: &mut MigrateHandle<'a>,
    // cx: &mut Rooted<'a, Context<'a>>,
        unimplemented!{}
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
    // bool: Mux<'a, C, bool, Output = bool>,
{
    type Output = ROMPort<T>;

    fn mux(
        bld: &impl Builder<'a>,
        c: C::Repr,
        t: ROMPortRepr<'a, T>,
        e: ROMPortRepr<'a, T>,
    ) -> ROMPortRepr<'a, T> {
        // let ca: TWire<C> = TWire::new(c.clone());
        // let cv: TWire<C> = TWire::new(c);
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
        ROMPortRepr{ addr, val }
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

pub struct ROM<'a, T>
where
    T: Repr<'a>,
    // where
    //     T: for<'b> LazySecret<'b> + for<'b> SecretDep<'b, Decoded = T> + Clone,
    //     <T as Repr<'a>>::Repr: Copy + Clone,
{
    ports: Vec<TWire<'a, ROMPort<T>>>,
    length: u64,
}

impl<'a, T: Repr<'a> + Lit<'a>> Lit<'a> for ROMPort<T>
// where
//     <T as Repr<'a>>::Repr: std::marker::Copy,
{
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
    // T: typed::Eq<'a>,
    T: for<'b> LazySecret<'b>,
    // T: Repr<'a>,
    <T as Repr<'a>>::Repr: Copy,
    T: for<'b> SecretDep<'b, Decoded = T>,
{
    pub fn load(&mut self, b: &impl Builder<'a>, index: TWire<'a, u64>) -> TWire<'a, T> {
        // - Assert that index is in bounds ()
        // For now we assume that every input is in bounds
        // addr = index
        // let addr = index;
        // create a secret for the value
        // let inp = TWire::<(u64, Vec<ROMPort<T>>)>::new((
        //     index,
        //     TWire::new(self.ports[..self.length as usize].to_vec()),
        // ));

        // let map_to_index: fn(<(u64, Vec<ROMPort<T>>) as SecretDep<'a>>::Decoded) -> T =
        //     |(i, w)| w[i as usize].val.clone();

        // let val: TWire<'a, T> = b.secret_derived_sized(&[self.length as usize], inp, map_to_index);

        // let val: TWire<'a, T> = self.ports[0].val;
        // let val: TWire<'a, T> = b.secret_derived(addr, |i| {
        //     self.ports[0].val
        // });

        // let val: TWire<'a, T> = b.secret_derived(self.ports[0], |p| {
        //     p.val
        // });

        let ports: Vec<TWire<ROMPort<T>>> = self
            .ports
            .iter()
            .map(|w| {
                TWire::new(ROMPortRepr {
                    addr: w.repr.addr,
                    val: w.repr.val,
                })
            })
            .collect();
        let ports: TWire<'a, Vec<ROMPort<T>>> = TWire::new(ports);
        let inp: TWire<(u64, Vec<ROMPort<T>>)> = TWire::new((index, ports));
        // let ports: TWire<'a, Vec<ROMPort<T>>> = TWire::new(self.ports.clone());
        // JP: Should this be `secret_derived`?
        let val: TWire<'a, T> = b.secret_derived_sized(&[self.ports.len()], inp, move |(i, ps)| {
            ps[i as usize].val.clone()
        });

        // let ports: TWire<'a, Vec<u32>> = TWire::new(vec![0,1,2,3]);
        // let ports: TWire<'a, Vec<u32>> = b.lit(vec![0,1,2,3]);
        // let val: TWire<'a, u32> = b.secret_derived_sized(&[ports.len()], ports, move |ps:Vec<u32>| {
        //     ps[0]
        // });

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
    // T: Repr<'a>,
    <T as Repr<'a>>::Repr: Copy,
    // ROMPort<T>: Mux<'a, bool>,
    T: Mux<'a, bool, T, Output = T>,
    T: ToWireList<'a>,
    T: FromWireList<'a>,
    // T: Mux<'a, bool>,
    // where
    //     T: Repr<'a> + for<'b> LazySecret<'b>,
    // T: for<'b> LazySecret<'b>, //  + for<'b> SecretDep<'b, Decoded = T> + Clone + 'static,
    //     <T as Repr<'a>>::Repr: Copy + Clone,
{
    pub fn new(b: &impl Builder<'a>, values: Vec<TWire<'a, T>>) -> ROM<'a, T> {
        let length = values.len() as u64;
        let ports = values
            .into_iter()
            .enumerate()
            .map(|(i, v)| {
                TWire::new(ROMPortRepr {
                    addr: b.lit(i as u64),
                    val: v,
                })
            })
            .collect();
        ROM { ports, length }
    }

    pub fn finalize(self, b: &'a impl Builder<'a>) -> TWire<bool> {
        // Create secrets for sorted ROMPorts
        // If prover, sort ROMPorts and set corresponding secrets

        // JP: Why does ROMPort need to implement LE?
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
        // and that no read operations where out-of-bounds.
        if self.length > 0 {
            let is_final_address = b.eq(
                sorted_ports[sorted_ports.len() - 1].addr,
                b.lit(self.length - 1),
            );

            res = b.and(res, is_final_address);
        }
        // Build permutation check that ROMPorts and sorted ROMPorts are permutation
        // Assert that the final address is equal to the length - 1.
        res
    }
}

// impl<'a, T> FromIterator<TWire<'a, T>> for ROM<'a, T>
// where
//     T: for<'b> LazySecret<'b> + for<'b> SecretDep<'b, Decoded = T> + Clone,
//     <T as Repr<'a>>::Repr: Copy + Clone,
// {
//     fn from_iter<I: IntoIterator<Item = TWire<'a, T>>>(iter: I) -> Self {
//         unimplemented! {}
//     }
// }
