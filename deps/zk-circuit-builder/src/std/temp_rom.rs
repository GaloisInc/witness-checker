use crate::ir::{
    circuit::{Bits, CircuitTrait, Ty},
    typed::{Builder, BuilderExt, FromWireList, LazySecret, Lit, Repr, SecretDep, TWire, ToWireList},
};

use crate::ir::circuit::Wire;

use std::iter::FromIterator;

pub struct ROMPort<T> {
    pub addr: u64,
    pub val: T,
}

// #[derive(Copy)]
pub struct ROMPortRepr<'a, T: Repr<'a>>
// where
//     <T as Repr<'a>>::Repr: std::marker::Copy,
{
    pub addr: TWire<'a, u64>,
    pub val: TWire<'a, T>,
}

// impl<'a, T: Repr<'a>> Clone for ROMPortRepr<'a, T>
// where
//     <T as Repr<'a>>::Repr: std::marker::Copy,
// {
//     fn clone(&self) -> Self {
//         unimplemented!()
//     }
// }

impl<'a, T: Repr<'a>> Repr<'a> for ROMPort<T>
// where
//     <T as Repr<'a>>::Repr: std::marker::Copy,
{
    type Repr = ROMPortRepr<'a, T>;
}

// impl<'a, T: Repr<'a>> ToWireList<'a> for ROMPort<T>
impl<'a, T> ToWireList<'a> for ROMPort<T>
where
    T: Repr<'a>,
//     <T as Repr<'a>>::Repr: std::marker::Copy,
{
    fn num_wires(x: &Self::Repr) -> usize {
        // u32::num_wires(x)
        unimplemented!()
    }
    fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
        // u32::for_each_wire(x, f);
        unimplemented!()
    }
    fn num_sizes(x: &Self::Repr) -> usize {
        // u32::num_sizes(x)
        unimplemented!()
    }
    fn for_each_size(x: &Self::Repr, f: impl FnMut(usize)) {
        // u32::for_each_size(x, f);
        unimplemented!()
    }
}

impl<'a, T> FromWireList<'a> for ROMPort<T>
where
    T: Repr<'a>
{
    fn expected_num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize { unimplemented!{} }

    fn for_each_expected_wire_type<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        _sizes: &mut impl Iterator<Item = usize>,
        mut f: impl FnMut(Ty<'a>),
    ) {
        // f(Self::wire_type(c))
        unimplemented!{}
    }

    fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        sizes: &mut impl Iterator<Item = usize>,
        build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
    ) -> Self::Repr {
        unimplemented!{}
    }
}
impl<'a, T> SecretDep<'a> for ROMPort<T>
where
    T: Repr<'a>,
// where
//     T: for<'b> LazySecret<'b> + for<'b> SecretDep<'b, Decoded = T> + Clone,
//     <T as Repr<'a>>::Repr: Copy + Clone,
{
    type Decoded = ROMPort<T>;
    fn from_bits_iter(
        sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> Self {
        unimplemented!{}
        // ROMPort {
        //     addr: u64::from_bits_iter(sizes, bits),
        //     val: T::from_bits_iter(sizes, bits),
        // }
    }
}

impl<'a, T> LazySecret<'a> for ROMPort<T>
where
    T: Repr<'a> + LazySecret<'a>,
{
    fn expected_word_len(_sizes: &mut impl Iterator<Item = usize>) -> usize {
        unimplemented!{}
    }
    fn word_len(&self) -> usize {
        unimplemented!{}
    }
    fn push_words(&self, out: &mut Vec<u32>) {
        unimplemented!{}
    }
}
        


pub struct ROM<'a, T>
where
    T:Repr<'a>,
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
    T: for<'b> LazySecret<'b>,
    // T: Repr<'a>,
    <T as Repr<'a>>::Repr: Copy,
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

        let ports: Vec<TWire<ROMPort<T>>> = self.ports.iter().map(|w| {
            TWire::new(ROMPortRepr {
                addr: w.repr.addr,
                val: w.repr.val,
            })
        }).collect();
        let ports: TWire<'a, Vec<ROMPort<T>>> = TWire::new(ports);
        let inp: TWire::<(u64, Vec<ROMPort<T>>)> = TWire::new((index, ports));
        // let ports: TWire<'a, Vec<ROMPort<T>>> = TWire::new(self.ports.clone());
        // JP: Should this be `secret_derived`?
        let val: TWire<'a, T> = b.secret_derived_sized(&[self.ports.len()], inp, move |(i,ps)| {
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

    pub fn finalize(self, b: &impl Builder<'a>) {
        // Create secrets for sorted ROMPorts
        // If prover, sort ROMPorts and set corresponding secrets
        // In circuit, check that the secrets are sorted
        // Build permutation check that ROMPorts and sorted ROMPorts are permutation
        // Assert that the final address is equal to the length - 1.

        // mh: &mut MigrateHandle<'a>,
        // cx: &mut Rooted<'a, Context<'a>>,
        unimplemented! {}
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
