//! Automatic migration of stack variables.
//!
//! The `CircuitExt::erase_and_migrate` method provides a way to garbage-collect unused `Wire`s,
//! but requires the caller to pass all live wire-containing values into the `erase_and_migrate`
//! call so that all wires can be updated.  To use this method effectively not only requires
//! converting recursive algorithms to iterative ones, it also requires lifting all iteration to
//! top level.
//!
//! This module provides a different approach.  The `MigrateHandle` type allows the caller to
//! register wire-containing values that are located on the stack (using the `root` method), and
//! traverses all such values automatically when `erase_and_migrate` is called.  There is some
//! extra effort required to manage `Rooted` values, but this is only required within the few
//! functions that (directly or indirectly) call `erase_and_migrate`.
//!
//! `Rooted` values must be explicitly "opened" for access.  The lifetimes are arranged to ensure
//! that it is impossible to call `erase_and_migrate` while any `Rooted` values are currently open.
use std::cell::RefCell;
use std::marker::PhantomData;
use std::mem;
use std::ops::{Deref, DerefMut};
use std::ptr;
use crate::ir::circuit::{CircuitTrait, CircuitExt, MigrateVisitor, EraseVisitor};
use crate::ir::migrate::{self, Migrate};


pub struct MigrateHandle<'a> {
    mcx: &'a MigrateContext<'a>,
}


pub struct MigrateContext<'a> {
    inner: RefCell<MigrateContextInner<'a>>,
}

pub struct Rooted<'a, T> {
    ptr: *mut T,
    mcx: &'a MigrateContext<'a>,
}

pub struct Open<'h, 'r, T> {
    ptr: &'r mut T,
    _marker: PhantomData<(&'h (), &'r mut ())>,
}

pub struct ProjectRooted<'a, 'b, T> {
    inner: Rooted<'a, T>,
    _marker: PhantomData<&'b mut ()>,
}


impl<'a> MigrateContext<'a> {
    pub fn new() -> MigrateContext<'a> {
        MigrateContext {
            inner: RefCell::new(MigrateContextInner::new()),
        }
    }

    fn alloc<T: Migrate<'a, 'a, Output = T>>(&self, x: T) -> *mut T {
        self.inner.borrow_mut().alloc(x)
    }

    /// Free `ptr`, which was produced by `self.alloc`.  Allocations must follow stack discipline:
    /// the last object allocated must be the first one freed.  If `ptr` is not the last allocated
    /// object, this method will panic.
    fn free<T>(&self, ptr: *mut T) {
        self.inner.borrow_mut().free(ptr)
    }

    fn take<T>(&self, ptr: *mut T) -> T {
        self.inner.borrow_mut().take(ptr)
    }

    pub fn push_borrow<T>(&self, ptr: *mut T) {
        self.inner.borrow_mut().push_borrow(ptr);
    }

    fn migrate_in_place(&self, v: &mut MigrateVisitor<'a, 'a>) {
        self.inner.borrow_mut().migrate_in_place(v)
    }

    fn erase_in_place(&self, v: &mut EraseVisitor<'a>) {
        self.inner.borrow_mut().erase_in_place(v)
    }
}

impl<'a> MigrateHandle<'a> {
    pub fn new(mcx: &'a MigrateContext<'a>) -> MigrateHandle<'a> {
        MigrateHandle { mcx }
    }

    pub fn root<T: Migrate<'a, 'a, Output = T>>(&self, x: T) -> Rooted<'a, T> {
        Rooted::from_context(x, self.mcx)
    }

    /// Open a `Rooted` value to access its value.
    ///
    /// The `Open` struct holds two borrows: a borrow of `self` (lifetime `'h`) which ensures that
    /// no `Open`s are outstanding at the time of `self.erase_and_migrate()`, and a borrow of
    /// `rooted` (lifetime `'r`) which ensures there is at most one outstanding `Open` for each
    /// `Rooted` location.
    pub fn open<'h, 'r, T>(&'h self, rooted: &'r mut Rooted<'a, T>) -> Open<'h, 'r, T>
    where 'a: 'h {
        unsafe {
            Open {
                ptr: &mut *rooted.ptr,
                _marker: PhantomData,
            }
        }
    }

    /// Erase and migrate all `Rooted` values.
    ///
    /// The caller is responsible for ensuring that values containing references into the circuit
    /// arena (indicated by the `'a` lifetime) are always wrapped in `Rooted`.  If any references
    /// with `'a` lifetime are accessible outside of a `Rooted` wrapper, those references may be
    /// left dangling after calling this method.
    pub unsafe fn erase_and_migrate<C: CircuitTrait<'a> + ?Sized>(&mut self, c: &'a C) {
        c.erase_with(|v| self.mcx.erase_in_place(v));
        c.migrate_with(|v| self.mcx.migrate_in_place(v));
    }
}

impl<'a, T: Migrate<'a, 'a, Output = T>> Rooted<'a, T> {
    /// Equivalent to `mh.root(x)`, but with an argument order that's more convenient in some
    /// cases.  With this constructor, `mh` is not borrowed during the evaluation of `x`, so code
    /// like the following is valid:
    ///
    /// ```Rust,ignore
    /// let x = Rooted::new({
    ///     // This call mutably borrows `mh`:
    ///     mh.erase_and_migrate(c);
    /// }, mh);
    /// ```
    pub fn new(x: T, mh: &MigrateHandle<'a>) -> Rooted<'a, T> {
        mh.root(x)
    }

    pub fn from_context(x: T, mcx: &'a MigrateContext<'a>) -> Rooted<'a, T> {
        let ptr = mcx.alloc(x);
        Rooted { ptr, mcx }
    }
}

impl<'a, T> Rooted<'a, T> {
    pub fn open<'r, 'h>(&'r mut self, mh: &'h MigrateHandle<'a>) -> Open<'h, 'r, T> {
        mh.open(self)
    }

    pub fn take(&mut self) -> T {
        self.mcx.take(self.ptr)
    }

    pub fn project<'b, U, F>(&'b mut self, f: F) -> ProjectRooted<'a, 'b, U>
    where F: for<'c> FnOnce(&'c mut T) -> &'c mut U {
        unsafe {
            let ptr: *mut U = f(&mut *self.ptr);
            self.mcx.push_borrow(ptr);
            ProjectRooted {
                inner: Rooted { ptr, mcx: self.mcx },
                _marker: PhantomData,
            }
        }
    }
}

impl<'a, T> Drop for Rooted<'a, T> {
    fn drop(&mut self) {
        self.mcx.free(self.ptr);
    }
}

impl<'a, T> Deref for ProjectRooted<'a, '_, T> {
    type Target = Rooted<'a, T>;
    fn deref(&self) -> &Rooted<'a, T> {
        &self.inner
    }
}

impl<'a, T> DerefMut for ProjectRooted<'a, '_, T> {
    fn deref_mut(&mut self) -> &mut Rooted<'a, T> {
        &mut self.inner
    }
}

impl<T> Deref for Open<'_, '_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.ptr }
    }
}

impl<T> DerefMut for Open<'_, '_, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.ptr }
    }
}


struct MigrateContextInner<'a> {
    stack: Vec<(*mut (), &'static Vtable)>,
    _marker: PhantomData<&'a &'a ()>,
}

impl<'a> MigrateContextInner<'a> {
    pub fn new() -> MigrateContextInner<'a> {
        MigrateContextInner {
            stack: Vec::new(),
            _marker: PhantomData,
        }
    }

    pub fn alloc<T>(&mut self, x: T) -> *mut T
    where T: Migrate<'a, 'a, Output = T> {
        unsafe {
            let ptr = Box::into_raw(Box::new(x));
            let vtable = Vtable::get::<T>(self);
            self.stack.push((ptr as *mut (), vtable));
            ptr
        }
    }

    pub fn free<T>(&mut self, ptr: *mut T) {
        unsafe {
            let (ptr2, vtable) = self.stack.pop().unwrap();
            assert_eq!(ptr as *mut (), ptr2);
            (vtable.drop_box)(ptr as *mut ());
        }
    }

    pub fn take<T>(&mut self, ptr: *mut T) -> T {
        unsafe {
            // FIXME: avoid linear scan
            let &mut (_, ref mut vtable) = self.stack.iter_mut()
                .filter(|& &mut (ptr2, _)| ptr2 == ptr as *mut ())
                .next().unwrap();
            assert!(
                *vtable as *const _ != Vtable::get_dummy::<T>() as *const _,
                "can't take this Rooted value",
            );
            *vtable = Vtable::get_dummy::<T>();
            // FIXME: this leaks the allocation
            ptr::read(ptr)
        }
    }

    pub fn push_borrow<T>(&mut self, ptr: *mut T) {
        let dummy_vtable = Vtable::get_dummy::<T>();
        self.stack.push((ptr as *mut (), dummy_vtable));
    }

    pub fn migrate_in_place(&mut self, v: &mut MigrateVisitor<'a, 'a>) {
        unsafe {
            for &(ptr, vtable) in &self.stack {
                (vtable.migrate_in_place)(ptr, v as *mut _ as *mut () as *mut _);
            }
        }
    }

    pub fn erase_in_place(&mut self, v: &mut EraseVisitor<'a>) {
        unsafe {
            for &(ptr, vtable) in &self.stack {
                (vtable.erase_in_place)(ptr, v as *mut _ as *mut () as *mut _);
            }
        }
    }
}


struct Vtable {
    drop_box: unsafe fn(*mut ()),
    migrate_in_place: unsafe fn(*mut (), *mut MigrateVisitor<'static, 'static>),
    erase_in_place: unsafe fn(*mut (), *mut EraseVisitor<'static>),
}

impl Vtable {
    fn get<'a, T: Migrate<'a, 'a, Output = T>>(mcxi: &MigrateContextInner<'a>) -> &'static Vtable {
        &Vtable {
            drop_box: |ptr| unsafe {
                drop(Box::from_raw(ptr as *mut T))
            },
            migrate_in_place: |ptr, v| unsafe {
                migrate::migrate_in_place(
                    &mut *(v as *mut () as *mut MigrateVisitor<'a, 'a>),
                    &mut *(ptr as *mut T),
                );
            },
            erase_in_place: |ptr, v| unsafe {
                migrate::migrate_in_place(
                    &mut *(v as *mut () as *mut EraseVisitor<'a>),
                    &mut *(ptr as *mut T),
                );
            },
        }
    }

    fn get_dummy<T>() -> &'static Vtable {
        &Vtable {
            drop_box: |_| {},
            migrate_in_place: |_, _| {},
            erase_in_place: |_, _| {},
        }
    }
}
