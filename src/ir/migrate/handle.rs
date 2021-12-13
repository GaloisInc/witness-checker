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
use std::alloc::Layout;
use std::any;
use std::cell::RefCell;
use std::marker::PhantomData;
use std::mem::{self, MaybeUninit};
use std::ops::{Deref, DerefMut};
use std::ptr;
use crate::ir::circuit::{CircuitTrait, CircuitExt, MigrateVisitor, EraseVisitor};
use crate::ir::migrate::{self, Migrate};


pub struct MigrateHandle<'a> {
    mcx: &'a MigrateContext<'a>,
    prev_size: usize,
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

/// Thin wrapper used for `Rooted::project`.  This is identical to `&'a mut T`, but avoids holding
/// an actual `&mut` across `MigrateHandle::erase_and_migrate`, which would cause an aliasing
/// violation.
pub struct Projected<'a, T> {
    ptr: *mut T,
    _marker: PhantomData<&'a mut T>,
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

    fn alloc_no_migrate<T>(&self, x: T) -> *mut T {
        self.inner.borrow_mut().alloc_no_migrate(x)
    }

    /// Free `ptr`, which was produced by `self.alloc`.
    unsafe fn free<T>(&self, ptr: *mut T) {
        self.inner.borrow_mut().free(ptr)
    }

    unsafe fn take<T>(&self, ptr: *mut T) -> T {
        self.inner.borrow_mut().take(ptr)
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
        MigrateHandle {
            mcx,
            prev_size: 1024 * 1024,
        }
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
            assert!(!rooted.ptr.is_null());
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
        if c.as_base().arena_size() > 2 * self.prev_size {
            c.erase_with(|v| self.mcx.erase_in_place(v));
            c.migrate_with(|v| self.mcx.migrate_in_place(v));
            self.prev_size = c.as_base().arena_size();
        }
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
        unsafe {
            let ptr = mem::replace(&mut self.ptr, ptr::null_mut());
            self.mcx.take(ptr)
        }
    }

    pub fn project<'b, U, F>(
        &'b mut self,
        mh: &MigrateHandle<'a>,
        f: F,
    ) -> Rooted<'a, Projected<'b, U>>
    where F: for<'c> FnOnce(&'c mut T) -> &'c mut U {
        unsafe {
            let inner = f(&mut *self.ptr);
            let ptr = self.mcx.alloc_no_migrate(Projected {
                ptr: inner,
                _marker: PhantomData,
            });
            Rooted { ptr, mcx: self.mcx }
        }
    }
}

impl<'a, T> Drop for Rooted<'a, T> {
    fn drop(&mut self) {
        unsafe {
            if !self.ptr.is_null() {
                self.mcx.free(self.ptr);
            }
        }
    }
}

impl<T> Deref for Projected<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.ptr }
    }
}

impl<T> DerefMut for Projected<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.ptr }
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
    head: *mut StorageHeader,
    tail: *mut StorageHeader,
    _marker: PhantomData<&'a &'a ()>,
}

struct StorageHeader {
    prev: *mut StorageHeader,
    next: *mut StorageHeader,
    vtable: &'static Vtable,
}

#[repr(C)]
struct Storage<T> {
    header: StorageHeader,
    data: T,
}

impl<T> Storage<T> {
    pub fn new(vtable: &'static Vtable, x: T) -> Storage<T> {
        Storage {
            header: StorageHeader {
                prev: ptr::null_mut(),
                next: ptr::null_mut(),
                vtable,
            },
            data: x,
        }
    }

    pub fn from_data_ptr_raw(ptr: *mut T) -> *mut Storage<T> {
        unsafe {
            let (_, off) = Self::layout_and_data_offset();
            (ptr as *mut u8).sub(off) as *mut Storage<T>
        }
    }

    fn layout_and_data_offset() -> (Layout, usize) {
        let (l, off) = Layout::new::<StorageHeader>()
            .extend(Layout::new::<T>()).unwrap();
        (l.pad_to_align(), off)
    }
}

impl<'a> MigrateContextInner<'a> {
    pub fn new() -> MigrateContextInner<'a> {
        MigrateContextInner {
            head: ptr::null_mut(),
            tail: ptr::null_mut(),
            _marker: PhantomData,
        }
    }

    fn debug_check_list(&self) {
        unsafe {
            if self.head.is_null() {
                assert!(self.tail.is_null());
                return;
            } else {
                assert!(!self.tail.is_null());
            }

            let mut cur = self.head;
            while !cur.is_null() {
                if !(*cur).next.is_null() {
                    assert_eq!((*(*cur).next).prev, cur);
                } else {
                    assert_eq!(cur, self.tail);
                }

                if !(*cur).prev.is_null() {
                    assert_eq!((*(*cur).prev).next, cur);
                } else {
                    assert_eq!(cur, self.head);
                }

                cur = (*cur).next;
            }
        }
    }

    unsafe fn append(&mut self, node: *mut StorageHeader) {
        (*node).prev = self.tail;
        (*node).next = ptr::null_mut();
        if !self.tail.is_null() {
            (*self.tail).next = node;
        }
        self.tail = node;
        if self.head.is_null() {
            self.head = node;
        }

        if cfg!(debug_assertions) {
            self.debug_check_list();
        }
    }

    unsafe fn remove(&mut self, node: *mut StorageHeader) {
        if self.head == node {
            self.head = (*node).next;
        }
        if self.tail == node {
            self.tail = (*node).prev;
        }
        if !(*node).prev.is_null() {
            (*(*node).prev).next = (*node).next;
        }
        if !(*node).next.is_null() {
            (*(*node).next).prev = (*node).prev;
        }

        if cfg!(debug_assertions) {
            self.debug_check_list();
        }
    }

    unsafe fn alloc_with_vtable<T>(&mut self, x: T, vtable: &'static Vtable) -> *mut T {
        unsafe {
            let node = Box::into_raw(Box::new(Storage::new(vtable, x)));
            self.append(&mut (*node).header);
            let ptr = &mut (*node).data;
            ptr
        }
    }

    pub fn alloc<T>(&mut self, x: T) -> *mut T
    where T: Migrate<'a, 'a, Output = T> {
        unsafe {
            let vtable = Vtable::get::<T>(self);
            self.alloc_with_vtable(x, vtable)
        }
    }

    /// Allocate a node with a value of type `T`, but ignore it when erasing/migrating nodes.  This
    /// is useful for `Rooted::project`: the resulting reference needs to be wrapped in `Rooted` so
    /// we can track its usage via `Rooted::open`, but it doesn't need to be migrated (the value it
    /// points to will already be migrated thanks to its own entry in the list).
    pub fn alloc_no_migrate<T>(&mut self, x: T) -> *mut T {
        unsafe {
            let vtable = Vtable::get_no_migrate::<T>();
            self.alloc_with_vtable(x, vtable)
        }
    }

    pub unsafe fn free<T>(&mut self, ptr: *mut T) {
        unsafe {
            let node = Storage::from_data_ptr_raw(ptr);
            self.remove(&mut (*node).header);
            let vtable = (*node).header.vtable;
            (vtable.drop_box)(node as *mut Storage<()>);
        }
    }

    pub unsafe fn take<T>(&mut self, ptr: *mut T) -> T {
        unsafe {
            let node = Storage::from_data_ptr_raw(ptr);
            let vtable = (*node).header.vtable;
            self.remove(&mut (*node).header);
            let mut dest = MaybeUninit::uninit();
            (vtable.take_box)(node as *mut Storage<()>, dest.as_ptr() as *mut ());
            dest.assume_init()
        }
    }

    pub fn migrate_in_place(&mut self, v: &mut MigrateVisitor<'a, 'a>) {
        unsafe {
            let v_ptr = v as *mut _ as *mut () as *mut _;
            let mut node = self.head;
            while !node.is_null() {
                let vtable = (*node).vtable;
                (vtable.migrate_in_place)(node as *mut Storage<()>, v_ptr);
                node = (*node).next;
            }
        }
    }

    pub fn erase_in_place(&mut self, v: &mut EraseVisitor<'a>) {
        unsafe {
            let v_ptr = v as *mut _ as *mut () as *mut _;
            let mut node = self.head;
            while !node.is_null() {
                let vtable = (*node).vtable;
                (vtable.erase_in_place)(node as *mut Storage<()>, v_ptr);
                node = (*node).next;
            }
        }
    }
}


struct Vtable {
    /// `drop_box(ptr)`: Reconstitute `ptr` as a `Box<T>` and drop it.
    drop_box: unsafe fn(*mut Storage<()>),
    /// `take_box(ptr, dest)`: Reconstitute `ptr` as a `Box<T>` and move its value into `*dest`.
    /// On return, `*dest` is always initialized.
    take_box: unsafe fn(*mut Storage<()>, *mut ()),
    /// `migrate_in_place(ptr, v)`: Apply visitor `v` to `*ptr` in-place.
    migrate_in_place: unsafe fn(*mut Storage<()>, *mut MigrateVisitor<'static, 'static>),
    /// `erase_in_place(ptr, v)`: Apply visitor `v` to `*ptr` in-place.
    erase_in_place: unsafe fn(*mut Storage<()>, *mut EraseVisitor<'static>),
}

impl Vtable {
    fn get<'a, T: Migrate<'a, 'a, Output = T>>(mcxi: &MigrateContextInner<'a>) -> &'static Vtable {
        &Vtable {
            drop_box: |ptr| unsafe {
                drop(Box::from_raw(ptr as *mut Storage<T>))
            },
            take_box: |ptr, dest| unsafe {
                let x = Box::from_raw(ptr as *mut Storage<T>).data;
                ptr::write(dest as *mut T, x);
            },
            migrate_in_place: |ptr, v| unsafe {
                migrate::migrate_in_place(
                    &mut *(v as *mut () as *mut MigrateVisitor<'a, 'a>),
                    &mut (*(ptr as *mut Storage<T>)).data,
                );
            },
            erase_in_place: |ptr, v| unsafe {
                migrate::migrate_in_place(
                    &mut *(v as *mut () as *mut EraseVisitor<'a>),
                    &mut (*(ptr as *mut Storage<T>)).data,
                );
            },
        }
    }

    fn get_no_migrate<T>() -> &'static Vtable {
        &Vtable {
            drop_box: |ptr| unsafe {
                drop(Box::from_raw(ptr as *mut Storage<T>))
            },
            take_box: |ptr, dest| unsafe {
                let x = Box::from_raw(ptr as *mut Storage<T>).data;
                ptr::write(dest as *mut T, x);
            },
            migrate_in_place: |_, _| unsafe {},
            erase_in_place: |_, _| unsafe {},
        }
    }
}
