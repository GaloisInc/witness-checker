use crate::ir::{
    circuit::Bits,
    typed::{Builder, BuilderExt, LazySecret, Lit, Repr, SecretDep, TWire, ToWireList},
};

use crate::ir::circuit::Wire;

use std::iter::FromIterator;

pub struct ROMPort<T> {
    pub addr: u64,
    pub val: T,
}

#[derive(Copy)]
pub struct ROMPortRepr<'a, T: Repr<'a>>
where
    <T as Repr<'a>>::Repr: std::marker::Copy,
{
    pub addr: TWire<'a, u64>,
    pub val: TWire<'a, T>,
}

impl<'a, T: Repr<'a>> Clone for ROMPortRepr<'a, T> 
where
    <T as Repr<'a>>::Repr: std::marker::Copy,
{
    fn clone(&self) -> Self {
        unimplemented!()
    }
}

impl<'a, T: Repr<'a>> Repr<'a> for ROMPort<T>
where
    <T as Repr<'a>>::Repr: std::marker::Copy,
{
    type Repr = ROMPortRepr<'a, T>;
}

impl<'a, T: Repr<'a>> ToWireList<'a> for ROMPort<T>
where
    <T as Repr<'a>>::Repr: std::marker::Copy,
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

impl<'a, T: Repr<'a> + SecretDep<'a, Decoded = T>> SecretDep<'a> for ROMPort<T>
where
    <T as Repr<'a>>::Repr: std::marker::Copy,
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

pub struct ROM<'a, T: Repr<'a>>
where
    <T as Repr<'a>>::Repr: std::marker::Copy,
{
    ports: Vec<TWire<'a, ROMPort<T>>>,
    length: u64,
}

impl<'a, T: Repr<'a> + Lit<'a>> Lit<'a> for ROMPort<T>
where
    <T as Repr<'a>>::Repr: std::marker::Copy,
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
    // T: for<'b> LazySecret<'b>,
    <T as Repr<'a>>::Repr: Copy,
    // T: for<'b> SecretDep<'b, Decoded = T>,
    T: Clone + Repr<'a>,
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

    pub fn load(&mut self, b: &impl Builder<'a>, index: TWire<'a, u64>) -> TWire<'a, T>
    where
    //     <T as Repr<'a>>::Repr: Clone,
        T: SecretDep<'a, Decoded = T>,
        T: for<'b> LazySecret<'b>,
    {
        // - Assert that index is in bounds ()
        // For now we assume that every input is in bounds
        // addr = index
        let addr = index;
        // create a secret for the value
        let inp = TWire::<(u64, Vec<ROMPort<T>>)>::new((
                index,
                TWire::new(self.ports[..self.length as usize].to_vec()),
            ));
        let val = b.secret_derived_sized(
            &[self.length as usize],
            inp,
            |(i, w): (u64, Vec<ROMPort<T>>)| w[i as usize].val.clone(),
        );
        // create a new rom port
        let port = TWire::new(ROMPortRepr { addr, val });
        // add it to the vec
        self.ports.push(port);
        val
    }

    pub fn assert_consistent(self, b: &impl Builder<'a>) {
        // Create secrets for sorted ROMPorts
        // If prover, sort ROMPorts and set corresponding secrets
        // In circuit, check that the secrets are sorted
        // Build permutation check that ROMPorts and sorted ROMPorts are permutation

        // mh: &mut MigrateHandle<'a>,
        // cx: &mut Rooted<'a, Context<'a>>,
        unimplemented! {}
    }
}

impl<'a, T: Repr<'a>> FromIterator<TWire<'a, T>> for ROM<'a, T>
where
    <T as Repr<'a>>::Repr: std::marker::Copy,
{
    fn from_iter<I: IntoIterator<Item = TWire<'a, T>>>(iter: I) -> Self {
        unimplemented! {}
    }
}
