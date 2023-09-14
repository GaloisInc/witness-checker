
use crate::ir::typed::{Builder, TWire, Repr};

use std::marker::PhantomData;

pub struct ROM<'a,T> {
    phantom: PhantomData<&'a T>,
}

impl<'a, T: Repr<'a>> ROM<'a, T> {
    pub fn new(_b: &impl Builder<'a>, _values: &[TWire<'a, T>]) -> ROM<'a, T> {
        ROM {
            phantom: PhantomData,
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

