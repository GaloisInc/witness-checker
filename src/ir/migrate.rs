use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::Hash;
use std::mem::MaybeUninit;
use crate::ir::circuit::{DynCircuit, Wire, SecretHandle};
use crate::ir::typed::{TWire, Repr};

pub use cheesecloth_derive_migrate::{Migrate, impl_migrate_trivial};
use super::migrate;

pub trait Migrate<'a, 'b> {
    type Output;
    fn migrate<V: Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Self::Output;
}

pub trait Visitor<'a, 'b> {
    fn new_circuit(&self) -> &DynCircuit<'a>;

    fn visit<T: Migrate<'a, 'b>>(&mut self, x: T) -> T::Output {
        Migrate::migrate(x, self)
    }

    fn visit_wire(&mut self, w: Wire<'a>) -> Wire<'b>;
    fn visit_secret_handle(&mut self, sh: SecretHandle<'a>) -> SecretHandle<'b>;

    /// A "weak reference" version of `visit_wire`.  The visitor may return `None` on any call.
    /// For example, a garbage-collecting visitor might return `None` for old wires that have no
    /// corresponding new wire.
    fn visit_wire_weak(&mut self, w: Wire<'a>) -> Option<Wire<'b>> {
        Some(self.visit_wire(w))
    }
}

impl<'a, 'b> Migrate<'a, 'b> for Wire<'a> {
    type Output = Wire<'b>;

    fn migrate<V: Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Wire<'b> {
        v.visit_wire(self)
    }
}

impl<'a, 'b> Migrate<'a, 'b> for SecretHandle<'a> {
    type Output = SecretHandle<'b>;

    fn migrate<V: Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> SecretHandle<'b> {
        v.visit_secret_handle(self)
    }
}

impl<'a, 'b, T> Migrate<'a, 'b> for TWire<'a, T>
where
    T: for<'c> Repr<'c>,
    <T as Repr<'a>>::Repr: Migrate<'a, 'b, Output = <T as Repr<'b>>::Repr>,
{
    type Output = TWire<'b, T>;

    fn migrate<V: Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> TWire<'b, T> {
        TWire {
            repr: v.visit(self.repr),
        }
    }
}

impl<'a, 'b, T: Migrate<'a, 'b>> Migrate<'a, 'b> for Option<T> {
    type Output = Option<T::Output>;

    fn migrate<V: Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Option<T::Output> {
        self.map(|x| v.visit(x))
    }
}

impl<'a, 'b, T: Migrate<'a, 'b>> Migrate<'a, 'b> for Box<T> {
    type Output = Box<T::Output>;

    fn migrate<V: Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Box<T::Output> {
        Box::new(v.visit(*self))
    }
}

// There is no impl for `Rc<T>`, since in general it's not clear how to handle aliasing in general.
// Different types may want different behavior.  For example, `Rc<RefCell<Vec<bool>>>` should
// probably simply be cloned, so if it aliased any non-migrated `Rc`s, it will continue to do so.
// But `Rc<RefCell<Vec<Wire<'a>>>>` can't be cloned (we need to change the `'a` to `'b`), and may
// need to be migrated to produce a separate set of aliasing `Rc`s.

impl<'a, 'b, T: Migrate<'a, 'b>> Migrate<'a, 'b> for Vec<T> {
    type Output = Vec<T::Output>;

    fn migrate<V: Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Vec<T::Output> {
        self.into_iter().map(|x| v.visit(x)).collect()
    }
}

impl<'a, 'b, T: Migrate<'a, 'b>> Migrate<'a, 'b> for HashSet<T>
where T::Output: Eq + Hash {
    type Output = HashSet<T::Output>;

    fn migrate<V: Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> HashSet<T::Output> {
        self.into_iter().map(|x| v.visit(x)).collect()
    }
}

impl<'a, 'b, T: Migrate<'a, 'b>, U: Migrate<'a, 'b>> Migrate<'a, 'b> for HashMap<T, U>
where T::Output: Eq + Hash {
    type Output = HashMap<T::Output, U::Output>;

    fn migrate<V: Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> HashMap<T::Output, U::Output> {
        self.into_iter().map(|x| v.visit(x)).collect()
    }
}

impl<'a, 'b, T: Migrate<'a, 'b>, U: Migrate<'a, 'b>> Migrate<'a, 'b> for BTreeMap<T, U>
where T::Output: Ord {
    type Output = BTreeMap<T::Output, U::Output>;

    fn migrate<V: Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> BTreeMap<T::Output, U::Output> {
        self.into_iter().map(|x| v.visit(x)).collect()
    }
}

impl<'a, 'b, T: Migrate<'a, 'b>> Migrate<'a, 'b> for RefCell<T> {
    type Output = RefCell<T::Output>;

    fn migrate<V: Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> RefCell<T::Output> {
        RefCell::new(v.visit(self.into_inner()))
    }
}

impl_migrate_trivial!(u8);
impl_migrate_trivial!(u16);
impl_migrate_trivial!(u32);
impl_migrate_trivial!(u64);
impl_migrate_trivial!(u128);
impl_migrate_trivial!(usize);

impl_migrate_trivial!(i8);
impl_migrate_trivial!(i16);
impl_migrate_trivial!(i32);
impl_migrate_trivial!(i64);
impl_migrate_trivial!(i128);
impl_migrate_trivial!(isize);

impl_migrate_trivial!(f32);
impl_migrate_trivial!(f64);

impl_migrate_trivial!(bool);
impl_migrate_trivial!(char);

impl_migrate_trivial!(String);

macro_rules! impl_migrate_tuple {
    ($($A:ident),*) => {
        impl<'a, 'b, $($A: Migrate<'a, 'b>,)*> Migrate<'a, 'b> for ($($A,)*) {
            type Output = ($($A::Output,)*);

            fn migrate<V: Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> ($($A::Output,)*) {
                #![allow(bad_style)]
                #![allow(unused)]   // `v`, in the zero-element case
                let ($($A,)*) = self;
                ($(v.visit($A),)*)
            }
        }
    };
}

impl_migrate_tuple!();
impl_migrate_tuple!(A);
impl_migrate_tuple!(A, B);
impl_migrate_tuple!(A, B, C);
impl_migrate_tuple!(A, B, C, D);
impl_migrate_tuple!(A, B, C, D, E);
impl_migrate_tuple!(A, B, C, D, E, F);
impl_migrate_tuple!(A, B, C, D, E, F, G);
impl_migrate_tuple!(A, B, C, D, E, F, G, H);
impl_migrate_tuple!(A, B, C, D, E, F, G, H, I);
impl_migrate_tuple!(A, B, C, D, E, F, G, H, I, J);

macro_rules! impl_migrate_array {
    ($($N:expr),*) => {
        $(
            impl<'a, 'b, T: Migrate<'a, 'b>> Migrate<'a, 'b> for [T; $N] {
                type Output = [T::Output; $N];

                fn migrate<V: Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> [T::Output; $N] {
                    unsafe {
                        let old = MaybeUninit::new(self);
                        let mut new = MaybeUninit::uninit();
                        let old_ptr = old.as_ptr() as *const T;
                        let new_ptr = new.as_mut_ptr() as *mut T::Output;
                        for i in 0..$N {
                            new_ptr.add(i).write(v.visit(old_ptr.add(i).read()));
                        }
                        new.assume_init()
                    }
                }
            }
        )*
    };
}

impl_migrate_array!(
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
    10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
    30, 31, 32
);

