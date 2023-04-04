//! Types for constructing circuits, gates, and wires.
//!
//! `Circuit` is the main context/builder type for constructing circuits.  It's defined in three
//! layers:
//!
//! * `CircuitBase` provides the lowest-level API for interning gates, types, and so on.
//! * The `Circuit`/`CircuitRef` types add support for filters, which can perform local rewrites on
//!   the circuit as gates are constructed.  This is used for optimization.  The `CircuitTrait`
//!   trait abstracts over `Circuit` and `CircuitRef`.
//! * The `CircuitExt` trait adds higher-level helper methods, so callers can use convenient
//!   `add`/`sub` methods instead of manually constructing a `GateKind::Add`.
use std::alloc::Layout;
use std::any::{self, Any, TypeId, type_name};
use std::cell::{self, Cell, RefCell, UnsafeCell};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem::{self, ManuallyDrop};
use std::ptr;
use std::ops::{Deref, DerefMut, Range};
use std::slice;
use std::str;
use bumpalo::Bump;
use log::info;
use num_bigint::{BigUint, BigInt, Sign};
use crate::eval::{self, Evaluator, CachingEvaluator};
use crate::ir::migrate::{self, Migrate, Visitor as _};
use crate::util::CowBox;


// CircuitBase layer

pub struct Arenas {
    arena: UnsafeCell<Bump>,
}

pub struct CircuitBase<'a> {
    arenas: &'a Arenas,
    // TODO: clean up interning
    // Currently it's possible to get two distinct interned pointers for the same value (e.g.,
    // `ty1` and `ty2` where `ty1 != ty2` but `*ty1 == *ty2`) by creating two different `Circuit`s
    // backed by the same arena.  We should have a combined structure that owns both the arena and
    // the interning tables, though that might require a bit of unsafe code.
    intern_gate: RefCell<HashSet<&'a Gate<'a>>>,
    intern_ty: RefCell<HashSet<&'a TyKind<'a>>>,
    intern_wire_list: RefCell<HashSet<&'a [Wire<'a>]>>,
    intern_ty_list: RefCell<HashSet<&'a [Ty<'a>]>>,
    intern_gadget_kind: RefCell<HashSet<&'a HashDynGadgetKind<'a>>>,
    intern_str: RefCell<HashSet<&'a str>>,
    intern_bits: RefCell<HashSet<&'a [u32]>>,

    function_scope: RefCell<Option<FunctionScope<'a>>>,

    current_label: Cell<&'a str>,
    is_prover: bool,
    functions: RefCell<Vec<Function<'a>>>,
    secret_type: TypeId,
}

struct FunctionScope<'a> {
    secrets: Vec<(SecretInputId, Ty<'a>)>,
}

impl<'a> CircuitBase<'a> {
    pub fn new<S: 'static>(arenas: &'a Arenas, is_prover: bool) -> CircuitBase<'a> {
        let c = CircuitBase {
            arenas,
            intern_gate: RefCell::new(HashSet::new()),
            intern_ty: RefCell::new(HashSet::new()),
            intern_wire_list: RefCell::new(HashSet::new()),
            intern_ty_list: RefCell::new(HashSet::new()),
            intern_gadget_kind: RefCell::new(HashSet::new()),
            intern_str: RefCell::new(HashSet::new()),
            intern_bits: RefCell::new(HashSet::new()),
            function_scope: RefCell::new(None),
            current_label: Cell::new(""),
            is_prover,
            functions: RefCell::new(Vec::new()),
            secret_type: TypeId::of::<S>(),
        };
        c.preload_common();
        c
    }

    fn preload_common(&self) {
        self.preload_common_types();
        self.preload_common_bits();
        self.preload_common_strs();
    }

    fn preload_common_types(&self) {
        let mut intern = self.intern_ty.borrow_mut();
        for &ty in COMMON_TYPES {
            intern.insert(ty);
        }
    }

    fn preload_common_bits(&self) {
        let mut intern = self.intern_bits.borrow_mut();
        for &bits in COMMON_BITS {
            intern.insert(bits);
        }
    }

    fn preload_common_strs(&self) {
        let mut intern = self.intern_str.borrow_mut();
        intern.insert("");
    }

    pub unsafe fn with_secret_type_unchecked<'b, S: 'static>(
        &'b self,
    ) -> &'b CircuitBaseWithSecretType<'a, S> {
        mem::transmute(self)
    }

    pub fn with_secret_type<S: 'static>(&self) -> Option<&CircuitBaseWithSecretType<'a, S>> {
        unsafe {
            if self.secret_type == TypeId::of::<S>() {
                Some(self.with_secret_type_unchecked())
            } else {
                None
            }
        }
    }

    fn arena(&self) -> &'a Bump {
        self.arenas.arena()
    }

    /// Size metric for deciding when to garbage collect (`erase_and_migrate`).
    ///
    /// For determinism, we use the gate count rather than the arena size.  The arena size will be
    /// different between the prover and the verifier since the prover allocates `Bits` for secret
    /// wires.  This means using arena size would cause GC decisions to happen differently, causing
    /// one side to have `Erased` where the other side has an actual gate.  Then any optimization
    /// that inspects the unequal gates might produce unequal results.
    pub fn gc_size(&self) -> usize {
        self.intern_gate.borrow().len()
    }

    fn intern_gate(&self, gate: Gate<'a>) -> &'a Gate<'a> {
        let mut intern = self.intern_gate.borrow_mut();
        match intern.get(&gate) {
            Some(x) => x,
            None => {
                let gate = self.arena().alloc(gate);
                intern.insert(gate);
                gate
            },
        }
    }

    fn intern_ty(&self, ty: TyKind<'a>) -> &'a TyKind<'a> {
        let mut intern = self.intern_ty.borrow_mut();
        match intern.get(&ty) {
            Some(x) => x,
            None => {
                let ty = self.arena().alloc(ty);
                intern.insert(ty);
                ty
            },
        }
    }

    fn intern_wire_list(&self, wire_list: &[Wire<'a>]) -> &'a [Wire<'a>] {
        let mut intern = self.intern_wire_list.borrow_mut();
        match intern.get(wire_list) {
            Some(&x) => x,
            None => {
                let wire_list = self.arena().alloc_slice_copy(wire_list);
                intern.insert(wire_list);
                wire_list
            },
        }
    }

    fn intern_ty_list(&self, ty_list: &[Ty<'a>]) -> &'a [Ty<'a>] {
        let mut intern = self.intern_ty_list.borrow_mut();
        match intern.get(ty_list) {
            Some(&x) => x,
            None => {
                let ty_list = self.arena().alloc_slice_copy(ty_list);
                intern.insert(ty_list);
                ty_list
            },
        }
    }

    pub fn intern_bits(&self, b: &[u32]) -> Bits<'a> {
        let mut intern = self.intern_bits.borrow_mut();
        match intern.get(b) {
            Some(&x) => Bits(x),
            None => {
                let b = self.arena().alloc_slice_copy(b);
                intern.insert(b);
                Bits(b)
            },
        }
    }

    fn intern_str(&self, s: &str) -> &'a str {
        let mut intern = self.intern_str.borrow_mut();
        match intern.get(s) {
            Some(&x) => x,
            None => {
                let s_bytes = self.arena().alloc_slice_copy(s.as_bytes());
                let s = unsafe { str::from_utf8_unchecked(s_bytes) };
                intern.insert(s);
                s
            },
        }
    }

    /// Intern a gadget kind so it can be used to construct `Gadget` gates.  It's legal to intern
    /// the same `GadgetKind` more than once, so this can be used inside stateless lowering passes
    /// (among other things).
    fn intern_gadget_kind<G: GadgetKind<'a>>(&self, g: G) -> GadgetKindRef<'a> {
        let mut intern = self.intern_gadget_kind.borrow_mut();
        match intern.get(HashDynGadgetKind::new(&g)) {
            Some(&x) => {
                GadgetKindRef(&x.0)
            },
            None => {
                let g = self.arena().alloc(g);
                intern.insert(HashDynGadgetKind::new(g));
                GadgetKindRef(g)
            },
        }
    }


    fn gate(&self, kind: GateKind<'a>) -> Wire<'a> {
        // Forbid constructing gates that violate type-safety invariants.
        match kind {
            GateKind::Binary(op, a, b) => {
                assert!(
                    a.ty == b.ty,
                    "type mismatch for {:?}: {:?} != {:?}", op, a.ty, b.ty,
                );
            },
            GateKind::Shift(op, _, b) => match *b.ty {
                TyKind::Uint(_) => {},
                _ => panic!("{:?} shift amount must be a Uint, not {:?}", op, b.ty),
            },
            GateKind::Compare(op, a, b) => {
                assert!(
                    a.ty == b.ty,
                    "type mismatch for {:?}: {:?} != {:?}", op, a.ty, b.ty,
                );
            },
            GateKind::Mux(c, t, e) => {
                assert!(
                    *c.ty == TyKind::BOOL,
                    "mux condition must be {:?}, not {:?}", TyKind::BOOL, c.ty,
                );
                assert!(
                    t.ty == e.ty,
                    "type mismatch for mux: {:?} != {:?}", c.ty, e.ty,
                );
            },
            GateKind::Extract(w, i) => match *w.ty {
                TyKind::Bundle(tys) => {
                    if i >= tys.len() {
                        panic!(
                            "index out of range for extract: {} >= {} ({:?})",
                            i, tys.len(), tys,
                        );
                    }
                },
                _ => panic!("bad input type for extract: {:?} (expected Bundle)", w.ty),
            },
            // GateKind::Gadget typechecking happens in the call to `kind.ty`
            _ => {},
        }

        // Forbid using a single `Secret` in multiple gates.
        match kind {
            GateKind::Secret(s) => { s.set_used(); },
            GateKind::Call(_, _, ss) => {
                for &(_, s) in ss {
                    s.set_used();
                }
            },
            _ => {},
        }

        Wire(self.intern_gate(Gate {
            ty: kind.ty(self),
            kind,
            label: Label(self.current_label.get()),
            eval_hook: Unhashed(Cell::new(None)),
        }))
    }

    fn wire_list(&self, wire_list: &[Wire<'a>]) -> &'a [Wire<'a>] {
        self.intern_wire_list(wire_list)
    }

    fn ty(&self, kind: TyKind<'a>) -> Ty<'a> {
        Ty(self.intern_ty(kind))
    }

    fn ty_list(&self, ty_list: &[Ty<'a>]) -> &'a [Ty<'a>] {
        self.intern_ty_list(ty_list)
    }


    fn alloc_secret_init_fn<S: 'static, F>(&self, f: F) -> SecretInitFn<'a>
    where
        F: for<'b> Fn(&CircuitBase<'b>, &S, &[Bits<'b>]) -> Bits<'b>,
        F: Sized + Copy + 'static,
    {
        fn erase<S>(
            f: impl for<'b> Fn(&CircuitBase<'b>, &S, &[Bits<'b>]) -> Bits<'b> + Copy + 'static,
        ) -> impl for<'b> Fn(&CircuitBase<'b>, *const (), &[Bits<'b>]) -> Bits<'b> + Copy + 'static {
            move |c, secret, dep_vals| {
                unsafe {
                    let secret = &*(secret as *const S);
                    f(c, secret, dep_vals)
                }
            }
        }

        unsafe {
            let r = self.arena().alloc(erase::<S>(f));
            SecretInitFn::new(IsCopy::new_ref(r) as _)
        }
    }

    fn alloc_lazy_secret<S, F>(&self, ty: Ty<'a>, deps: &'a [Wire<'a>], init: F) -> Secret<'a>
    where
        S: 'static,
        F: for<'b> Fn(&CircuitBase<'b>, &S, &[Bits<'b>]) -> Bits<'b>,
        F: Sized + Copy + 'static,
    {
        // `S` must match this circuit's secret type.  As a special case, we also allow `()`, which
        // essentially means that the `&S` input will be ignored.  We don't allow other ZSTs here
        // because some ZSTs are used as markers, where having a value of that type means that some
        // property holds.
        assert!(TypeId::of::<S>() == self.secret_type ||
            TypeId::of::<S>() == TypeId::of::<()>());
        let sd = if self.is_prover {
            let init = self.alloc_secret_init_fn::<S, F>(init);
            SecretData::new_lazy_prover::<S>(ty, init, &[])
        } else {
            SecretData::new(ty, SecretValue::VerifierUnknown)
        };
        Secret(self.arena().alloc(sd))
    }


    fn alloc_secret_input(&self, ty: Ty<'a>) -> (Secret<'a>, SecretInputId) {
        let mut scope = self.function_scope.borrow_mut();
        let scope = scope.as_mut().expect("can't use alloc_secret_input outside function body");
        let id = SecretInputId(scope.secrets.len());
        scope.secrets.push((id, ty));
        let s = Secret(self.arena().alloc(SecretData::new(ty, SecretValue::FunctionInput(id))));
        (s, id)
    }

    fn alloc_secret(&self, ty: Ty<'a>, val: SecretValue<'a>) -> Secret<'a> {
        assert!(
            self.function_scope.borrow().is_none(),
            "can't use alloc_secret inside a function body",
        );
        Secret(self.arena().alloc(SecretData::new(ty, val)))
    }


    /// Add a new secret value to the witness, initialize it with the result of `mk_val()` (if
    /// running in prover mode), and return the resulting `Secret`.
    ///
    /// `mk_val` will not be called when running in prover mode.
    fn new_secret_init<T: AsBits, F>(&self, ty: Ty<'a>, mk_val: F) -> Secret<'a>
    where F: FnOnce() -> T {
        let val = SecretValue::init(self.is_prover, || self.bits(ty, mk_val()));
        self.alloc_secret(ty, val)
    }

    /// Create a new uninitialized secret.  When running in prover mode, the secret must be
    /// initialized later using `SecretData::set_from_lit`.
    fn new_secret_uninit(&self, ty: Ty<'a>) -> Secret<'a> {
        let val = SecretValue::uninit(self.is_prover);
        self.alloc_secret(ty, val)
    }

    /// Add a new secret value to the witness and return it.  The accompanying `SecretHandle` can
    /// be used to assign a value to the secret after construction.  If the `SecretHandle` is
    /// dropped without setting a value, the value will be set to zero automatically.
    fn new_secret(&self, ty: Ty<'a>) -> (Secret<'a>, SecretHandle<'a>) {
        let default = self.intern_bits(&[]);
        self.new_secret_default(ty, default)
    }

    /// Like `new_secret`, but dropping the `SecretHandle` without setting a value will set the
    /// value to `default` instead of zero.
    fn new_secret_default<T: AsBits>(
        &self,
        ty: Ty<'a>,
        default: T,
    ) -> (Secret<'a>, SecretHandle<'a>) {
        let secret = self.new_secret_uninit(ty);
        let default = self.bits(ty, default);
        let handle = SecretHandle::new(secret, default);
        (secret, handle)
    }

    /// Add a new secret input to the current function.  Panics if called at top level (outside a
    /// function definition).
    fn new_secret_input(&self, ty: Ty<'a>) -> (Secret<'a>, SecretInputId) {
        self.alloc_secret_input(ty)
    }


    /// Add a new secret value to the witness, and return a `Wire` that carries that value.  The
    /// accompanying `SecretHandle` can be used to assign a value to the secret after construction.
    /// If the `SecretHandle` is dropped without setting a value, the value will be set to zero
    /// automatically.
    fn new_secret_wire(&self, ty: Ty<'a>) -> (Wire<'a>, SecretHandle<'a>) {
        let (s, sh) = self.new_secret(ty);
        (self.secret(s), sh)
    }

    /// Like `new_secret_wire`, but dropping the `SecretHandle` without setting a value will set the
    /// value to `default` instead of zero.
    fn new_secret_wire_default<T: AsBits>(
        &self,
        ty: Ty<'a>,
        default: T,
    ) -> (Wire<'a>, SecretHandle<'a>) {
        let (s, sh) = self.new_secret_default(ty, default);
        (self.secret(s), sh)
    }

    /// Add a new secret value to the witness, initialize it with the result of `mk_val()` (if
    /// running in prover mode), and return a `Wire` that carries that value.
    ///
    /// `mk_val` will not be called when running in prover mode.
    fn new_secret_wire_init<T: AsBits, F>(&self, ty: Ty<'a>, mk_val: F) -> Wire<'a>
    where F: FnOnce() -> T {
        let s = self.new_secret_init(ty, mk_val);
        self.secret(s)
    }

    /// Create a new uninitialized secret.  When running in prover mode, the secret must be
    /// initialized later using `SecretData::set_from_lit`.
    fn new_secret_wire_uninit(&self, ty: Ty<'a>) -> Wire<'a> {
        let s = self.new_secret_uninit(ty);
        self.secret(s)
    }

    /// Add a new secret input to the current function.  Panics if called at top level (outside a
    /// function definition).
    fn new_secret_wire_input(&self, ty: Ty<'a>) -> (Wire<'a>, SecretInputId) {
        let (s, id) = self.alloc_secret_input(ty);
        (self.secret(s), id)
    }


    fn scoped_label_exact<T: fmt::Display>(&self, label: T) -> CellResetGuard<&'a str> {
        let new = self.intern_str(&label.to_string());
        CellResetGuard::new(&self.current_label, new)
    }

    fn current_label(&self) -> &'a str {
        self.current_label.get()
    }


    /// Replace the current arenas with new ones, and reset `*self` to a fresh circuit.  Returns
    /// the old `Arenas` and `Circuit`.  This is unsafe because dropping the returned `Arenas` will
    /// invalidate the `Circuit` and any outstanding references to values allocated there.
    unsafe fn take(&self) -> ArenasAndCircuit<'a> {
        let CircuitBase {
            ref arenas,
            ref intern_gate, ref intern_ty, ref intern_wire_list, ref intern_ty_list,
            ref intern_gadget_kind, ref intern_str, ref intern_bits,
            ref function_scope,
            ref current_label,
            is_prover,
            ref functions,
            secret_type,
        } = *self;

        let old_arenas = Box::new(arenas.take());

        let old_arenas_ptr: *const Arenas = &*old_arenas;
        let old_circuit = CircuitBase {
            arenas: &*old_arenas_ptr,
            intern_gate: RefCell::new(intern_gate.take()),
            intern_ty: RefCell::new(intern_ty.take()),
            intern_wire_list: RefCell::new(intern_wire_list.take()),
            intern_ty_list: RefCell::new(intern_ty_list.take()),
            intern_gadget_kind: RefCell::new(intern_gadget_kind.take()),
            intern_str: RefCell::new(intern_str.take()),
            intern_bits: RefCell::new(intern_bits.take()),
            function_scope: RefCell::new(function_scope.take()),
            current_label: Cell::new(current_label.replace("")),
            is_prover,
            functions: RefCell::new(functions.take()),
            secret_type,
        };

        self.preload_common();

        ArenasAndCircuit {
            arenas: ManuallyDrop::new(old_arenas),
            circuit: ManuallyDrop::new(old_circuit),
        }
    }
}

impl Arenas {
    pub fn new() -> Arenas {
        Arenas {
            arena: UnsafeCell::new(Bump::new()),
        }
    }

    fn arena(&self) -> &Bump {
        unsafe { &*self.arena.get() }
    }

    fn allocated_bytes(&self) -> usize {
        self.arena().allocated_bytes()
    }

    /// Replace `*self` with a new `Arenas`, and return `*self`.  This is unsafe because dropping
    /// the returned `Arenas` will invalidate any outstanding references to values allocated there.
    unsafe fn take(&self) -> Arenas {
        Arenas {
            arena: UnsafeCell::new(ptr::replace(self.arena.get(), Bump::new())),
        }
    }
}

/// Helper type for use during migration.  We use this to make sure the old `circuit` and `Arenas`
/// get dropped in the right order.  This is not safe for general use.
struct ArenasAndCircuit<'a> {
    arenas: ManuallyDrop<Box<Arenas>>,
    circuit: ManuallyDrop<CircuitBase<'a>>,
}

impl<'a> Drop for ArenasAndCircuit<'a> {
    fn drop(&mut self) {
        unsafe {
            ManuallyDrop::drop(&mut self.circuit);
            ManuallyDrop::drop(&mut self.arenas);
        }
    }
}


// Filtering layer

/// A high-level arithmetic/boolean circuit.
///
/// This circuit representation has no notion of a "public wire" - all wires carry secret values.
/// This works because we provide no "open" or "reveal" operation.  The only way to produce a
/// public/cleartext value is with `GateKind::Lit`, which contains a compile-time constant, so any
/// operations over literals can be computed entirely at compile time.
///
/// If a witness is available, the `Circuit` includes its values.  This allows circuit
/// transformations to make corresponding changes to the witness if necessary, such as splitting a
/// 64-bit secret into a pair of 32-bit secrets that together make up the original value.  The full
/// witness is not represented explicitly, but the individual values are accessible through the
/// `GateKind::Secret` gates present in the circuit.  Use the `walk_witness` function to obtain the
/// witness values that are used to compute some set of `Wire`s.
pub struct Circuit<'a, F: ?Sized> {
    base: CircuitBase<'a>,
    /// The filter is wrapped in an `UnsafeCell` so it can be mutated by the `migrate_filter`
    /// method.
    filter: UnsafeCell<F>,
}

impl<'a, F> Circuit<'a, F> {
    pub fn new<S: 'static>(arenas: &'a Arenas, is_prover: bool, filter: F) -> Circuit<'a, F> {
        Circuit {
            base: CircuitBase::new::<S>(arenas, is_prover),
            filter: UnsafeCell::new(filter),
        }
    }
}

impl<'a, F: CircuitFilter<'a> + ?Sized> Circuit<'a, F> {
    /// Define a function.  The closure receives a list of argument wires (of types `arg_tys`), and
    /// returns a wire representing the output of the function.  The secondary output of type `T`
    /// can be used to return a data structure describing the `SecretInputId`s used by this
    /// function.
    ///
    /// Concretely, the `Circuit` passed to the callback is `self` and uses the same lifetime `'a`,
    /// but we hide this fact from the caller so that `rustc` will report an error if wires from
    /// outside the function are used inside the callback or vice versa.
    //
    // This function is defined on the concrete `Circuit` type instead of the generic `CircuitExt`
    // trait because this lets it provide a more precise circuit type to the callback, which
    // simplifies its usage with `typed::Builder`.  However, it should be easy to copy into
    // `CircuitExt` if it's needed in the future.
    pub fn define_function_ex<F2, T>(
        &self,
        name: &str,
        arg_tys: &[Ty<'a>],
        f: F2,
    ) -> (Function<'a>, T)
    where F2: for<'b> FnOnce(&Circuit<'b, F>, &[Wire<'b>]) -> (Wire<'b>, T) {
        let function_scope = &self.base.function_scope;
        let old_scope = mem::replace(&mut *function_scope.borrow_mut(), Some(FunctionScope {
            secrets: Vec::new(),
        }));

        let arg_wires = arg_tys.iter().enumerate()
            .map(|(i, &ty)| self.gate(GateKind::Argument(i, ty)))
            .collect::<Vec<_>>();
        let (result_wire, extra) = f(self, &arg_wires);

        let new_scope = mem::replace(&mut *function_scope.borrow_mut(), old_scope).unwrap();
        let func = Function(self.as_base().arena().alloc(FunctionDef {
            name: self.as_base().intern_str(name),
            arg_tys: self.ty_list(arg_tys),
            secret_inputs: self.as_base().arena().alloc_slice_copy(&new_scope.secrets),
            result_wire,
        }));
        self.as_base().functions.borrow_mut().push(func);
        (func, extra)
    }

    pub fn define_function<F2>(&self, name: &str, arg_tys: &[Ty<'a>], f: F2) -> Function<'a>
    where F2: for<'b> FnOnce(&Circuit<'b, F>, &[Wire<'b>]) -> Wire<'b> {
        let (func, ()) = self.define_function_ex(
            name,
            arg_tys,
            |c, args| (f(c, args), ()),
        );
        func
    }
}

/// A reference to a `Circuit`, separated into base and filter components.  This is mainly used in
/// filter chains, to allow working with a subset of the full filter chain.
pub struct CircuitRef<'a, 'c, F: ?Sized> {
    pub base: &'c CircuitBase<'a>,
    pub filter: &'c F,
}

impl<'a, 'c, F: ?Sized> Clone for CircuitRef<'a, 'c, F> {
    fn clone(&self) -> Self { *self }
}

impl<'a, 'c, F: ?Sized> Copy for CircuitRef<'a, 'c, F> {}


pub trait CircuitTrait<'a> {
    fn as_base(&self) -> &CircuitBase<'a>;
    fn filter(&self) -> &dyn CircuitFilter<'a>;
    fn gate(&self, kind: GateKind<'a>) -> Wire<'a>;

    /// Internal helper function for `CircuitExt::migrate`.  This migrates the filter (if any) in
    /// place.  There must be no outstanding references to the filter.
    ///
    /// This will panic when called on a `CircuitRef`, which doesn't have ownership of its filter.
    unsafe fn migrate_filter(&self, v: &mut MigrateVisitor<'a, 'a, '_>);
    unsafe fn erase_filter(&self, v: &mut EraseVisitor<'a, '_>);
}

impl<'a> CircuitTrait<'a> for CircuitBase<'a> {
    fn as_base(&self) -> &CircuitBase<'a> { self }
    fn filter(&self) -> &dyn CircuitFilter<'a> { &FilterNil }

    fn gate(&self, kind: GateKind<'a>) -> Wire<'a> {
        self.gate(kind)
    }

    unsafe fn migrate_filter(&self, _v: &mut MigrateVisitor<'a, 'a, '_>) {}
    unsafe fn erase_filter(&self, _v: &mut EraseVisitor<'a, '_>) {}
}

impl<'a, F: CircuitFilter<'a> + ?Sized> CircuitTrait<'a> for Circuit<'a, F> {
    fn as_base(&self) -> &CircuitBase<'a> { &self.base }
    fn filter(&self) -> &dyn CircuitFilter<'a> {
        unsafe { (*self.filter.get()).as_dyn() }
    }

    fn gate(&self, kind: GateKind<'a>) -> Wire<'a> {
        self.filter().gate(&self.base, kind)
    }

    unsafe fn migrate_filter(&self, v: &mut MigrateVisitor<'a, 'a, '_>) {
        (*self.filter.get()).migrate_in_place(v)
    }
    unsafe fn erase_filter(&self, v: &mut EraseVisitor<'a, '_>) {
        (*self.filter.get()).erase_in_place(v)
    }
}

impl<'a, F: CircuitFilter<'a> + ?Sized> CircuitTrait<'a> for CircuitRef<'a, '_, F> {
    fn as_base(&self) -> &CircuitBase<'a> { self.base }
    fn filter(&self) -> &dyn CircuitFilter<'a> { self.filter.as_dyn() }

    fn gate(&self, kind: GateKind<'a>) -> Wire<'a> {
        self.filter.gate(self.base, kind)
    }

    unsafe fn migrate_filter(&self, _v: &mut MigrateVisitor<'a, 'a, '_>) {
        panic!("can't migrate CircuitRef");
    }
    unsafe fn erase_filter(&self, _v: &mut EraseVisitor<'a, '_>) {
        panic!("can't erase CircuitRef");
    }
}


pub type DynCircuit<'a> = Circuit<'a, dyn CircuitFilter<'a> + 'a>;
pub type DynCircuitRef<'a, 'c> = CircuitRef<'a, 'c, dyn CircuitFilter<'a> + 'c>;


pub trait CircuitFilter<'a> {
    fn as_dyn(&self) -> &(dyn CircuitFilter<'a> + 'a);

    fn migrate_in_place(&mut self, v: &mut MigrateVisitor<'a, 'a, '_>);
    fn erase_in_place(&mut self, v: &mut EraseVisitor<'a, '_>);

    fn gate(&self, c: &CircuitBase<'a>, kind: GateKind<'a>) -> Wire<'a>;

    fn add_pass<F>(self, func: F) -> FilterCons<F, Self>
    where
        Self: Sized,
        F: Fn(&CircuitRef<'a, '_, Self>, GateKind<'a>) -> Wire<'a>,
    {
        FilterCons { func, rest: self }
    }

    fn add_opt_pass<F>(self, active: bool, func: F) -> FilterConsOpt<F, Self>
    where
        Self: Sized,
        F: Fn(&CircuitRef<'a, '_, Self>, GateKind<'a>) -> Wire<'a>,
    {
        FilterConsOpt { func, active, rest: self }
    }
}

macro_rules! circuit_filter_common_methods {
    () => {
        fn as_dyn(&self) -> &(dyn CircuitFilter<'a> + 'a) { self }

        fn migrate_in_place(&mut self, v: &mut $crate::ir::circuit::MigrateVisitor<'a, 'a, '_>) {
            $crate::ir::migrate::migrate_in_place(v, self);
        }

        fn erase_in_place(&mut self, v: &mut $crate::ir::circuit::EraseVisitor<'a, '_>) {
            $crate::ir::migrate::migrate_in_place(v, self);
        }
    };
}

#[derive(Migrate)]
pub struct FilterNil;

impl<'a> CircuitFilter<'a> for FilterNil {
    circuit_filter_common_methods!();

    fn gate(&self, c: &CircuitBase<'a>, kind: GateKind<'a>) -> Wire<'a> {
        c.gate(kind)
    }
}

pub struct FilterCons<F1, F2> {
    func: F1,
    rest: F2,
}

impl<'a, F1, F2> CircuitFilter<'a> for FilterCons<F1, F2>
where
    F1: Fn(&CircuitRef<'a, '_, F2>, GateKind<'a>) -> Wire<'a> + 'static,
    F2: CircuitFilter<'a> + 'a,
    F2: Migrate<'a, 'a, Output = F2>,
{
    circuit_filter_common_methods!();

    fn gate(&self, c: &CircuitBase<'a>, kind: GateKind<'a>) -> Wire<'a> {
        let c = CircuitRef { base: c, filter: &self.rest };
        (self.func)(&c, kind)
    }
}

impl<'a, 'b, F1, F2> Migrate<'a, 'b> for FilterCons<F1, F2>
where
    F1: 'static,
    F2: Migrate<'a, 'b>,
{
    type Output = FilterCons<F1, F2::Output>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Self::Output {
        FilterCons {
            func: self.func,
            rest: v.visit(self.rest),
        }
    }
}

pub struct FilterConsOpt<F1, F2> {
    func: F1,
    active: bool,
    rest: F2,
}

impl<'a, F1, F2> CircuitFilter<'a> for FilterConsOpt<F1, F2>
where
    F1: Fn(&CircuitRef<'a, '_, F2>, GateKind<'a>) -> Wire<'a> + 'static,
    F2: CircuitFilter<'a> + 'a,
    F2: Migrate<'a, 'a, Output = F2>,
{
    circuit_filter_common_methods!();

    fn gate(&self, c: &CircuitBase<'a>, kind: GateKind<'a>) -> Wire<'a> {
        if self.active {
            let c = CircuitRef { base: c, filter: &self.rest };
            (self.func)(&c, kind)
        } else {
            self.rest.gate(c, kind)
        }
    }
}

impl<'a, 'b, F1, F2> Migrate<'a, 'b> for FilterConsOpt<F1, F2>
where
    F1: 'static,
    F2: Migrate<'a, 'b>,
{
    type Output = FilterConsOpt<F1, F2::Output>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Self::Output {
        FilterConsOpt {
            func: self.func,
            active: self.active,
            rest: v.visit(self.rest),
        }
    }
}


// Utility layer

pub trait CircuitExt<'a>: CircuitTrait<'a> {
    fn is_prover(&self) -> bool {
        self.as_base().is_prover
    }

    fn as_ref(&self) -> DynCircuitRef<'a, '_> {
        CircuitRef { base: self.as_base(), filter: self.filter() }
    }


    fn ty(&self, kind: TyKind<'a>) -> Ty<'a> {
        self.as_base().ty(kind)
    }

    fn ty_list(&self, ty_list: &[Ty<'a>]) -> &'a [Ty<'a>] {
        self.as_base().ty_list(ty_list)
    }

    fn ty_bundle(&self, tys: &[Ty<'a>]) -> Ty<'a> {
        self.ty(TyKind::Bundle(self.ty_list(tys)))
    }

    fn ty_bundle_iter<I>(&self, it: I) -> Ty<'a>
    where I: IntoIterator<Item = Ty<'a>> {
        let tys = it.into_iter().collect::<Vec<_>>();
        self.ty_bundle(&tys)
    }


    fn bits<T: AsBits>(&self, ty: Ty<'a>, val: T) -> Bits<'a> {
        let sz = match *ty {
            TyKind::Int(sz) | TyKind::Uint(sz) => sz,
            TyKind::GF(f) => f.bit_size(),
            _ => panic!("can't construct bit representation for non-primitive type {:?}", ty),
        };
        let val = val.as_bits(self.as_base(), sz);
        assert!(val.width() <= sz.bits());
        val
    }


    /// Add a new secret value to the witness, initialize it with the result of `mk_val()` (if
    /// running in prover mode), and return a `Secret` that carries that value.
    ///
    /// `mk_val` will not be called when running in prover mode.
    fn new_secret_init<T: AsBits, F>(&self, ty: Ty<'a>, mk_val: F) -> Secret<'a>
    where F: FnOnce() -> T {
        self.as_base().new_secret_init(ty, mk_val)
    }

    /// Create a new uninitialized secret.  When running in prover mode, the secret must be
    /// initialized later using `SecretData::set_from_lit`.
    fn new_secret_uninit(&self, ty: Ty<'a>) -> Secret<'a> {
        self.as_base().new_secret_uninit(ty)
    }

    /// Add a new secret value to the witness, and return a `Secret` that carries that value.  The
    /// accompanying `SecretHandle` can be used to assign a value to the secret after construction.
    /// If the `SecretHandle` is dropped without setting a value, the value will be set to zero
    /// automatically.
    fn new_secret(&self, ty: Ty<'a>) -> (Secret<'a>, SecretHandle<'a>) {
        self.as_base().new_secret(ty)
    }

    /// Like `new_secret_wire`, but dropping the `SecretHandle` without setting a value will set the
    /// value to `default` instead of zero.
    fn new_secret_default<T: AsBits>(
        &self,
        ty: Ty<'a>,
        default: T,
    ) -> (Secret<'a>, SecretHandle<'a>) {
        self.as_base().new_secret_default(ty, default)
    }

    /// Add a new secret input to the current function.  Panics if called at top level (outside a
    /// function definition).
    fn new_secret_input(&self, ty: Ty<'a>) -> (Secret<'a>, SecretInputId) {
        self.as_base().new_secret_input(ty)
    }

    fn new_secret_lazy<S, F>(&self, ty: Ty<'a>, init: F) -> Secret<'a>
    where
        S: 'static,
        F: for<'b> Fn(&CircuitBase<'b>, &S) -> Bits<'b>,
        F: Sized + Copy + 'static,
    {
        self.as_base().alloc_lazy_secret(ty, &[], move |c, secret, _dep_vals| {
            init(c, secret)
        })
    }

    fn new_secret_derived<F>(&self, ty: Ty<'a>, deps: &'a [Wire<'a>], init: F) -> Secret<'a>
    where
        F: for<'b> Fn(&CircuitBase<'b>, &[Bits<'b>]) -> Bits<'b>,
        F: Sized + Copy + 'static,
    {
        self.as_base().alloc_lazy_secret::<(), _>(ty, deps, move |c, _secret, dep_vals| {
            init(c, dep_vals)
        })
    }


    /// Add a new secret value to the witness, initialize it with the result of `mk_val()` (if
    /// running in prover mode), and return a `Wire` that carries that value.
    ///
    /// `mk_val` will not be called when running in prover mode.
    fn new_secret_wire_init<T: AsBits, F>(&self, ty: Ty<'a>, mk_val: F) -> Wire<'a>
    where F: FnOnce() -> T {
        self.as_base().new_secret_wire_init(ty, mk_val)
    }

    /// Create a new uninitialized secret.  When running in prover mode, the secret must be
    /// initialized later using `SecretData::set_from_lit`.
    fn new_secret_wire_uninit(&self, ty: Ty<'a>) -> Wire<'a> {
        self.as_base().new_secret_wire_uninit(ty)
    }

    /// Add a new secret value to the witness, and return a `Wire` that carries that value.  The
    /// accompanying `SecretHandle` can be used to assign a value to the secret after construction.
    /// If the `SecretHandle` is dropped without setting a value, the value will be set to zero
    /// automatically.
    fn new_secret_wire(&self, ty: Ty<'a>) -> (Wire<'a>, SecretHandle<'a>) {
        self.as_base().new_secret_wire(ty)
    }

    /// Like `new_secret_wire`, but dropping the `SecretHandle` without setting a value will set the
    /// value to `default` instead of zero.
    fn new_secret_wire_default<T: AsBits>(
        &self,
        ty: Ty<'a>,
        default: T,
    ) -> (Wire<'a>, SecretHandle<'a>) {
        self.as_base().new_secret_wire_default(ty, default)
    }

    /// Add a new secret input to the current function.  Panics if called at top level (outside a
    /// function definition).
    fn new_secret_wire_input(&self, ty: Ty<'a>) -> (Wire<'a>, SecretInputId) {
        self.as_base().new_secret_wire_input(ty)
    }


    fn alloc_eval_hook_fn<F>(&self, f: F) -> EvalHookFn<'a>
    where
        F: Fn(&CircuitBase<'a>, &mut dyn eval::EvaluatorObj<'a>, Wire<'a>, Bits<'a>) + Copy + 'a,
    {
        let r = self.as_base().arena().alloc(f);
        EvalHookFn(r)
    }


    fn intern_gadget_kind<G: GadgetKind<'a>>(&self, g: G) -> GadgetKindRef<'a> {
        self.as_base().intern_gadget_kind(g)
    }


    fn wire_list(&self, wire_list: &[Wire<'a>]) -> &'a [Wire<'a>] {
        self.as_base().wire_list(wire_list)
    }

    fn lit<T: AsBits>(&self, ty: Ty<'a>, val: T) -> Wire<'a> {
        let val = self.bits(ty, val);
        self.gate(GateKind::Lit(val, ty))
    }

    fn secret(&self, secret: Secret<'a>) -> Wire<'a> {
        self.gate(GateKind::Secret(secret))
    }

    fn erased(&self, erased: Erased<'a>) -> Wire<'a> {
        self.gate(GateKind::Erased(erased))
    }

    fn unary(&self, op: UnOp, arg: Wire<'a>) -> Wire<'a> {
        self.gate(GateKind::Unary(op, arg))
    }

    fn neg(&self, arg: Wire<'a>) -> Wire<'a> {
        self.unary(UnOp::Neg, arg)
    }

    fn not(&self, arg: Wire<'a>) -> Wire<'a> {
        self.unary(UnOp::Not, arg)
    }

    fn binary(&self, op: BinOp, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.gate(GateKind::Binary(op, a, b))
    }

    fn add(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::Add, a, b)
    }

    fn sub(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::Sub, a, b)
    }

    fn mul(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::Mul, a, b)
    }

    fn div(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::Div, a, b)
    }

    fn mod_(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::Mod, a, b)
    }

    fn and(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::And, a, b)
    }

    fn or(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::Or, a, b)
    }

    fn all_true<I: Iterator<Item=Wire<'a>>>(&self, wires: I) -> Wire<'a> {
        let true_if_empty = self.lit(self.ty(TyKind::BOOL), 1);
        wires.fold(
            true_if_empty,
            |all_true, w| self.and(all_true, w),
        )
    }

    fn any_true<I: Iterator<Item=Wire<'a>>>(&self, wires: I) -> Wire<'a> {
        let false_if_empty = self.lit(self.ty(TyKind::BOOL), 0);
        wires.fold(
            false_if_empty,
            |any_true, w| self.or(any_true, w),
        )
    }

    fn xor(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.binary(BinOp::Xor, a, b)
    }

    fn shift(&self, op: ShiftOp, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.gate(GateKind::Shift(op, a, b))
    }

    fn shl(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.shift(ShiftOp::Shl, a, b)
    }

    fn shr(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.shift(ShiftOp::Shr, a, b)
    }

    fn compare(&self, op: CmpOp, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.gate(GateKind::Compare(op, a, b))
    }

    fn eq(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.compare(CmpOp::Eq, a, b)
    }

    fn ne(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.compare(CmpOp::Ne, a, b)
    }

    fn lt(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.compare(CmpOp::Lt, a, b)
    }

    fn le(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.compare(CmpOp::Le, a, b)
    }

    fn gt(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.compare(CmpOp::Gt, a, b)
    }

    fn ge(&self, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
        self.compare(CmpOp::Ge, a, b)
    }

    fn mux(&self, c: Wire<'a>, t: Wire<'a>, e: Wire<'a>) -> Wire<'a> {
        self.gate(GateKind::Mux(c, t, e))
    }

    fn cast(&self, w: Wire<'a>, ty: Ty<'a>) -> Wire<'a> {
        self.gate(GateKind::Cast(w, ty))
    }

    fn pack(&self, ws: &[Wire<'a>]) -> Wire<'a> {
        let ws = self.wire_list(ws);
        self.gate(GateKind::Pack(ws))
    }

    fn pack_iter<I>(&self, it: I) -> Wire<'a>
    where I: IntoIterator<Item = Wire<'a>> {
        let ws = it.into_iter().collect::<Vec<_>>();
        self.pack(&ws)
    }

    fn extract(&self, w: Wire<'a>, i: usize) -> Wire<'a> {
        self.gate(GateKind::Extract(w, i))
    }

    fn gadget(&self, kind: GadgetKindRef<'a>, args: &[Wire<'a>]) -> Wire<'a> {
        let args = self.wire_list(args);
        self.gate(GateKind::Gadget(kind, args))
    }

    fn gadget_iter<I>(&self, kind: GadgetKindRef<'a>, it: I) -> Wire<'a>
    where I: IntoIterator<Item = Wire<'a>> {
        let args = it.into_iter().collect::<Vec<_>>();
        self.gadget(kind, &args)
    }

    fn call(
        &self,
        func: Function<'a>,
        args: &'a [Wire<'a>],
        secrets: &[(SecretInputId, Secret<'a>)],
    ) -> Wire<'a> {
        let secrets = self.as_base().arena().alloc_slice_copy(secrets);
        self.gate(GateKind::Call(func, args, secrets))
    }


    fn current_label(&self) -> &'a str {
        self.as_base().current_label()
    }

    fn scoped_label<T: fmt::Display>(&self, label: T) -> CellResetGuard<&'a str> {
        let old = self.current_label();
        self.as_base().scoped_label_exact(format_args!("{}/{}", old, label))
    }

    fn scoped_label_exact<T: fmt::Display>(&self, label: T) -> CellResetGuard<&'a str> {
        self.as_base().scoped_label_exact(label)
    }

    fn with_label<T: fmt::Display, F: FnOnce() -> R, R>(&self, label: T, f: F) -> R {
        let _g = self.scoped_label(label);
        f()
    }


    unsafe fn migrate_with<F, R>(&self, f: F) -> R
    where F: FnOnce(&mut MigrateVisitor<'a, 'a, '_>) -> R {
        let old = self.as_base().take();

        let new_circuit = self.as_base();
        let mut v = MigrateVisitor::new(&old.circuit, new_circuit);

        // Transfer parts of `old_circuit` into `self`, which has been cleared.
        assert!(old.circuit.function_scope.borrow().is_none(),
            "can't migrate inside define_function");
        let current_label = new_circuit.intern_str(old.circuit.current_label.get());
        new_circuit.current_label.set(current_label);
        // Note we visit functions in the order they were originally defined.  This ensures the
        // calls are topologically sorted.
        let functions = old.circuit.as_base().functions.borrow_mut()
            .iter().map(|&f| v.visit(f)).collect();
        *new_circuit.functions.borrow_mut() = functions;

        self.migrate_filter(&mut v);
        let r = f(&mut v);

        info!("migrated {} wires, {} secrets", v.wire_map.len(), v.secret_map.len());
        info!("  old size: {} bytes", old.arenas.allocated_bytes());
        info!("  new size: {} bytes", new_circuit.arena().allocated_bytes());

        drop(v);
        drop(old);

        r
    }

    /// Migrate all wires in `self` and `x` to a fresh arena.  Essentially, this garbage-collects
    /// all unused wires.
    ///
    /// This method is unsafe because it invalidates all other `Wire<'a>` values, leaving them as
    /// dangling references.  The caller is responsible for ensuring that there are no `Wire<'a>`
    /// values outside of `self` and `x`.  This also mutates the circuit filter (if any) in place,
    /// so the caller must ensure there are no outstanding references to the filter.
    ///
    /// This method will panic when called on a `CircuitRef`.  It should only be called when the
    /// concrete type is `CircuitBase` or `Circuit`.
    unsafe fn migrate<T: Migrate<'a, 'a, Output = T>>(
        &self,
        x: T,
    ) -> T {
        use crate::ir::migrate::Visitor;
        self.migrate_with(|v| v.visit(x))
    }

    unsafe fn erase_with<F: FnOnce(&mut EraseVisitor<'a, '_>) -> R, R>(
        &self,
        secret_value: CowBox<dyn Any>,
        f: F,
    ) -> (R, HashMap<Wire<'a>, Wire<'a>>) {
        let mut v = EraseVisitor::new(self.as_base(), secret_value);

        // Don't erase inside `self.functions`.
        self.erase_filter(&mut v);
        let r = f(&mut v);

        let erased_map = {
            let v = v;
            v.erased_map
        };

        (r, erased_map)
    }

    /// Replace all non-trivial top-level wires in `self` and `x` with `GateKind::Erased`.
    ///
    /// This method is unsafe because it mutates the circuit filter (if any) in place, so the
    /// caller must ensure there are no outstanding references to the filter.
    unsafe fn erase<T: Migrate<'a, 'a, Output = T>>(
        &self,
        secret_value: CowBox<dyn Any>,
        x: T,
    ) -> (T, HashMap<Wire<'a>, Wire<'a>>) {
        use crate::ir::migrate::Visitor;
        self.erase_with(secret_value, |v| v.visit(x))
    }

    /// Shorthand for `erase` followed by `migrate`.
    unsafe fn erase_and_migrate<T: Migrate<'a, 'a, Output = T>>(
        &self,
        secret_value: CowBox<dyn Any>,
        x: T,
    ) -> (T, HashMap<Wire<'a>, Wire<'a>>) {
        let x = self.erase(secret_value, x);
        let (x, erased_map) = self.migrate(x);
        (x, erased_map)
    }
}

impl<'a, C: CircuitTrait<'a> + ?Sized> CircuitExt<'a> for C {}


pub struct MigrateVisitor<'a, 'b, 'c> {
    old_circuit: &'c CircuitBase<'a>,
    new_circuit: &'c CircuitBase<'b>,

    wire_map: HashMap<Wire<'a>, Wire<'b>>,
    secret_map: HashMap<Secret<'a>, Secret<'b>>,
    erased_map: HashMap<Erased<'a>, Erased<'b>>,
    function_map: HashMap<Function<'a>, Function<'b>>,
}

impl<'a, 'b, 'c> MigrateVisitor<'a, 'b, 'c> {
    fn new(
        old_circuit: &'c CircuitBase<'a>,
        new_circuit: &'c CircuitBase<'b>,
    ) -> MigrateVisitor<'a, 'b, 'c> {
        MigrateVisitor {
            old_circuit,
            new_circuit,

            wire_map: HashMap::new(),
            secret_map: HashMap::new(),
            erased_map: HashMap::new(),
            function_map: HashMap::new(),
        }
    }
}

impl<'a, 'b> migrate::Visitor<'a, 'b> for MigrateVisitor<'a, 'b, '_> {
    fn old_circuit(&self) -> &CircuitBase<'a> {
        self.old_circuit
    }

    fn new_circuit(&self) -> &CircuitBase<'b> {
        self.new_circuit
    }

    fn visit_wire(&mut self, w: Wire<'a>) -> Wire<'b> {
        if let Some(&new) = self.wire_map.get(&w) {
            return new;
        }

        let new = Wire(self.new_circuit.intern_gate(self.visit((*w).clone())));
        self.wire_map.insert(w, new);
        new
    }

    fn visit_secret(&mut self, s: Secret<'a>) -> Secret<'b> {
        if let Some(&new) = self.secret_map.get(&s) {
            return new;
        }

        let new = Secret(self.new_circuit.arena().alloc(self.visit((*s).clone())));
        self.secret_map.insert(s, new);
        new
    }

    fn visit_erased(&mut self, e: Erased<'a>) -> Erased<'b> {
        if let Some(&new) = self.erased_map.get(&e) {
            return new;
        }

        let new = Erased(self.new_circuit.arena().alloc(self.visit((*e).clone())));
        self.erased_map.insert(e, new);
        new
    }

    fn visit_function(&mut self, f: Function<'a>) -> Function<'b> {
        if let Some(&new) = self.function_map.get(&f) {
            return new;
        }

        let new = Function(self.new_circuit.arena().alloc(self.visit((*f).clone())));
        self.function_map.insert(f, new);
        new
    }

    fn visit_wire_weak(&mut self, w: Wire<'a>) -> Option<Wire<'b>> {
        self.wire_map.get(&w).cloned()
    }
}


pub struct EraseVisitor<'a, 'c> {
    circuit: &'c CircuitBase<'a>,
    erased_map: HashMap<Wire<'a>, Wire<'a>>,
    /// Keep track of the order in which we visit wires so that the backend can visit in a
    /// deterministic order.
    ///
    /// Merely changing `erased_map` to a `BTreeMap` is not sufficient for determinism.  Iterating
    /// over a `BTreeMap` would give the wires in pointer order, but pointer order is not
    /// deterministic.  When the arena `mmap`s a block of memory to use for allocations, the kernel
    /// may place that block at any unused address, and that choice affects the ordering of
    /// pointers.
    erased_order: Vec<(Wire<'a>, Wire<'a>)>,
    ev: RefCell<CachingEvaluator<'a, 'c, eval::RevealSecrets>>,
}

impl<'a, 'c> EraseVisitor<'a, 'c> {
    fn new(
        circuit: &'c CircuitBase<'a>,
        secret_value: CowBox<'c, dyn Any>,
    ) -> EraseVisitor<'a, 'c> {
        EraseVisitor {
            circuit,
            erased_map: HashMap::new(),
            erased_order: Vec::new(),
            ev: RefCell::new(CachingEvaluator::with_cow_secret(secret_value)),
        }
    }

    pub fn evaluator(&self) -> cell::RefMut<CachingEvaluator<'a, 'c, eval::RevealSecrets>> {
        self.ev.borrow_mut()
    }
}

impl<'a> migrate::Visitor<'a, 'a> for EraseVisitor<'a, '_> {
    fn old_circuit(&self) -> &CircuitBase<'a> {
        self.circuit
    }

    fn new_circuit(&self) -> &CircuitBase<'a> {
        self.circuit
    }

    fn visit_wire(&mut self, w: Wire<'a>) -> Wire<'a> {
        match w.kind {
            // Erasing these wouldn't save much memory, if any.  We particularly want to leave
            // `Lit` intact so that constant folding can continue working.
            GateKind::Lit(..) |
            GateKind::Secret(..) |
            GateKind::Erased(..) => return w,
            _ => {},
        }

        if let Some(&e) = self.erased_map.get(&w) {
            return e;
        }

        let ed = if self.circuit.is_prover() {
            let (bits, secret) = match self.ev.get_mut().eval_wire_bits(self.circuit, w) {
                Ok(x) => x,
                Err(e) => {
                    // Losing track of the value for this wire will leave us unable to construct
                    // the witness.  We can't simply choose not to erase the wire because that
                    // would leave the `GateKind` visible to later rewrite passes, which could
                    // cause the prover and verifier circuits to diverge.
                    panic!("failed to evaluate erased wire {:?}: {:?}", w, e);
                },
            };
            ErasedData::new(w.ty, bits, secret)
        } else {
            ErasedData::new_unset(w.ty)
        };
        let ed = self.circuit.arena().alloc(ed);
        let e = self.circuit.erased(Erased(ed));
        self.erased_map.insert(w, e);
        self.erased_order.push((w, e));
        e
    }

    fn visit_secret(&mut self, s: Secret<'a>) -> Secret<'a> { s }
    fn visit_erased(&mut self, e: Erased<'a>) -> Erased<'a> { e }

    fn visit_function(&mut self, f: Function<'a>) -> Function<'a> {
        // Currently, we don't erase any wires inside of function definitions.  Function bodies are
        // always available.  If this turns out to be unnecessary. we could erase the function's
        // result wires here.
        f
    }
}

impl<'a> EraseVisitor<'a, '_> {
    pub fn erased(&self) -> &[(Wire<'a>, Wire<'a>)] {
        &self.erased_order
    }
}



pub struct WireDeps<'a> {
    inner: WireDepsInner<'a>,
}

enum WireDepsInner<'a> {
    Small(Range<u8>, [Option<Wire<'a>>; 3]),
    Large(slice::Iter<'a, Wire<'a>>),
}

impl<'a> WireDeps<'a> {
    pub fn zero() -> WireDeps<'a> {
        Self::small(0, [None, None, None])
    }

    fn one(a: Wire<'a>) -> WireDeps<'a> {
        Self::small(1, [Some(a), None, None])
    }

    fn two(a: Wire<'a>, b: Wire<'a>) -> WireDeps<'a> {
        Self::small(2, [Some(a), Some(b), None])
    }

    fn three(a: Wire<'a>, b: Wire<'a>, c: Wire<'a>) -> WireDeps<'a> {
        Self::small(3, [Some(a), Some(b), Some(c)])
    }

    fn small(n: u8, arr: [Option<Wire<'a>>; 3]) -> WireDeps<'a> {
        WireDeps {
            inner: WireDepsInner::Small(0..n, arr),
        }
    }

    fn many(ws: &'a [Wire<'a>]) -> WireDeps<'a> {
        WireDeps {
            inner: WireDepsInner::Large(ws.iter()),
        }
    }
}

impl<'a> Iterator for WireDepsInner<'a> {
    type Item = Wire<'a>;
    fn next(&mut self) -> Option<Wire<'a>> {
        match *self {
            WireDepsInner::Small(ref mut range, ref arr) => {
                let i = range.next()? as usize;
                arr.get(i).and_then(|&x| x)
            },
            WireDepsInner::Large(ref mut it) => it.next().cloned(),
        }
    }
}

impl<'a> DoubleEndedIterator for WireDepsInner<'a> {
    fn next_back(&mut self) -> Option<Wire<'a>> {
        match *self {
            WireDepsInner::Small(ref mut range, ref arr) => {
                let i = range.next_back()? as usize;
                arr.get(i).and_then(|&x| x)
            },
            WireDepsInner::Large(ref mut it) => it.next_back().cloned(),
        }
    }
}

impl<'a> Iterator for WireDeps<'a> {
    type Item = Wire<'a>;
    fn next(&mut self) -> Option<Wire<'a>> {
        self.inner.next()
    }
}

impl<'a> DoubleEndedIterator for WireDeps<'a> {
    fn next_back(&mut self) -> Option<Wire<'a>> {
        self.inner.next_back()
    }
}

pub fn wire_deps<'a>(w: Wire<'a>) -> WireDeps<'a> {
    gate_deps(w.kind)
}

pub fn gate_deps<'a>(gk: GateKind<'a>) -> WireDeps<'a> {
    match gk {
        GateKind::Lit(_, _) |
        GateKind::Secret(_) |
        GateKind::Erased(_) |
        GateKind::Argument(_, _) => WireDeps::zero(),
        GateKind::Unary(_, a) |
        GateKind::Cast(a, _) |
        GateKind::Extract(a, _) => WireDeps::one(a),
        GateKind::Binary(_, a, b) |
        GateKind::Shift(_, a, b) |
        GateKind::Compare(_, a, b) => WireDeps::two(a, b),
        GateKind::Mux(c, t, e) => WireDeps::three(c, t, e),
        GateKind::Pack(ws) |
        GateKind::Gadget(_, ws) |
        GateKind::Call(_, ws, _) => WireDeps::many(ws),
    }
}

pub fn wire_and_secret_deps<'a>(w: Wire<'a>) -> WireDeps<'a> {
    gate_and_secret_deps(w.kind)
}

pub fn gate_and_secret_deps<'a>(gk: GateKind<'a>) -> WireDeps<'a> {
    match gk {
        GateKind::Secret(s) => WireDeps::many(s.deps),
        _ => gate_deps(gk),
    }
}


#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
enum PostorderAction<T> {
    Visit(T),
    Emit(T),
}

pub struct PostorderIter<'a, F> {
    stack: Vec<PostorderAction<Wire<'a>>>,
    /// Wires that have already been yielded.  We avoid processing the same wire twice.
    seen: HashSet<Wire<'a>>,
    /// Visitor function, called on each wire.  Returns `(emit, deps)`; first, all wires listed in
    /// `deps` will be visited (if they haven't been visited already), then the wire itself will be
    /// emitted if `emit` is `true`.
    visit: F,
}

impl<'a, F, I> Iterator for PostorderIter<'a, F>
where
    F: FnMut(Wire<'a>) -> (bool, I),
    I: Iterator<Item = Wire<'a>>,
{
    type Item = Wire<'a>;
    fn next(&mut self) -> Option<Wire<'a>> {
        let PostorderIter { ref mut stack, ref mut seen, ref mut visit } = *self;

        while let Some(action) = stack.pop() {
            match action {
                PostorderAction::Visit(wire) => {
                    if seen.contains(&wire) {
                        continue;
                    }

                    let (emit, deps) = visit(wire);
                    if emit {
                        stack.push(PostorderAction::Emit(wire));
                    }
                    for child in deps {
                        stack.push(PostorderAction::Visit(child));
                    }
                },

                PostorderAction::Emit(wire) => {
                    if !seen.insert(wire) {
                        continue;
                    }
                    return Some(wire);
                },
            }
        }
        None
    }
}

pub fn walk_wires_ex<'a, I, F, I2>(wires: I, visit: F) -> impl Iterator<Item = Wire<'a>>
where
    I: IntoIterator<Item = Wire<'a>>,
    F: FnMut(Wire<'a>) -> (bool, I2),
    I2: Iterator<Item = Wire<'a>>,
{
    let mut stack = wires.into_iter().map(PostorderAction::Visit).collect::<Vec<_>>();
    stack.reverse();
    PostorderIter {
        stack,
        seen: HashSet::new(),
        visit,
    }
}

pub fn walk_wires<'a, I>(wires: I) -> impl Iterator<Item = Wire<'a>>
where I: IntoIterator<Item = Wire<'a>> {
    walk_wires_ex(wires, |w| (true, wire_deps(w)))
}

pub fn walk_wires_filtered<'a, I, F>(wires: I, mut filter: F) -> impl Iterator<Item = Wire<'a>>
where I: IntoIterator<Item = Wire<'a>>, F: FnMut(Wire<'a>) -> bool {
    walk_wires_ex(wires, move |w| {
        if filter(w) {
            (true, wire_deps(w))
        } else {
            (false, WireDeps::zero())
        }
    })
}

/// Visit all `Secret`s that are used in the computation of `wires`.  Yields each `Secret`
/// once, in some deterministic order (assuming `wires` itself is deterministic).
pub fn walk_witness<'a, I>(wires: I) -> impl Iterator<Item = Secret<'a>>
where I: IntoIterator<Item = Wire<'a>> {
    walk_wires(wires).filter_map(|w| match w.kind {
        GateKind::Secret(s) => Some(s),
        _ => None,
    })
}


#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct IntSize(pub u16);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum TyKind<'a> {
    Int(IntSize),
    Uint(IntSize),
    GF(Field),
    Bundle(&'a [Ty<'a>]),

    /// Raw bits, with no particular interpretation.  This type is not accepted as input by any
    /// gate, nor can it be included in a `Bundle`.  However, it can appear as the type of a
    /// `Secret` gate and in the dependency list of a derived secret.
    ///
    /// This is used to fit arbitrary intermediate values into the wire-based dependency tracking
    /// for derived secrets.  Suppose you have a function that takes many input wires, does an
    /// expensive computation on their values, and derives many secrets from the result.  It would
    /// be inefficient to repeat the expensive computation for each derived secret.  To avoid this,
    /// you can create an intermediate secret derived from all the inputs via the expensive
    /// computation, and then derive the many secrets from that result.  As the intermediate value
    /// might not make sense as a circuit value or fit into the normal circuit type system, we
    /// provide `RawBits` to use for it instead.
    RawBits,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
/// Finite fields.
pub enum Field {
    // Small binary fields.
    #[cfg(feature = "gf_scuttlebutt")]
    F40b,
    #[cfg(feature = "gf_scuttlebutt")]
    F45b,
    #[cfg(feature = "gf_scuttlebutt")]
    F56b,
    #[cfg(feature = "gf_scuttlebutt")]
    F63b,
    #[cfg(feature = "gf_scuttlebutt")]
    F64b,
}

impl Field {
    pub fn bit_size(&self) -> IntSize {
        match *self {
            #[cfg(feature = "gf_scuttlebutt")]
            Field::F40b => IntSize(64), // Small binary fields are u64s in scuttlebutt.
            #[cfg(feature = "gf_scuttlebutt")]
            Field::F45b => IntSize(64),
            #[cfg(feature = "gf_scuttlebutt")]
            Field::F56b => IntSize(64),
            #[cfg(feature = "gf_scuttlebutt")]
            Field::F63b => IntSize(64),
            #[cfg(feature = "gf_scuttlebutt")]
            Field::F64b => IntSize(64),
        }
    }
}

pub trait FromBits {
    fn from_bits<'a>(b:Bits<'a>) -> Self;
}

impl IntSize {
    pub fn bits(self) -> u16 {
        self.0
    }
}

impl TyKind<'_> {
    pub const I8: TyKind<'static> = TyKind::Int(IntSize(8));
    pub const I16: TyKind<'static> = TyKind::Int(IntSize(16));
    pub const I32: TyKind<'static> = TyKind::Int(IntSize(32));
    pub const I64: TyKind<'static> = TyKind::Int(IntSize(64));
    pub const U8: TyKind<'static> = TyKind::Uint(IntSize(8));
    pub const U16: TyKind<'static> = TyKind::Uint(IntSize(16));
    pub const U32: TyKind<'static> = TyKind::Uint(IntSize(32));
    pub const U64: TyKind<'static> = TyKind::Uint(IntSize(64));
    pub const BOOL: TyKind<'static> = TyKind::Uint(IntSize(1));

    pub fn get_galois_field(&self) -> Option<Field> {
        match *self {
            TyKind::Int(_) => None,
            TyKind::Uint(_) => None,
            TyKind::GF(f) => Some(f),
            TyKind::Bundle(_) => None,
            TyKind::RawBits => None,
        }
    }

    pub fn is_integer(&self) -> bool {
        match *self {
            TyKind::Int(_) => true,
            TyKind::Uint(_) => true,
            TyKind::GF(_) => false,
            TyKind::Bundle(_) => false,
            TyKind::RawBits => false,
        }
    }

    pub fn integer_size(&self) -> IntSize {
        match *self {
            TyKind::Int(sz) => sz,
            TyKind::Uint(sz) => sz,
            TyKind::GF(f) => f.bit_size(),
            TyKind::Bundle(_) |
            TyKind::RawBits => panic!("{:?} has no IntSize", self),
        }
    }

    pub fn is_int(&self) -> bool {
        match *self {
            TyKind::Int(_) => true,
            _ => false,
        }
    }

    pub fn is_uint(&self) -> bool {
        match *self {
            TyKind::Uint(_) => true,
            _ => false,
        }
    }

    pub fn transfer<'b>(&self, c: &CircuitBase<'b>) -> Ty<'b> {
        match *self {
            TyKind::Uint(sz) => c.ty(TyKind::Uint(sz)),
            TyKind::Int(sz) => c.ty(TyKind::Int(sz)),
            TyKind::GF(f) => c.ty(TyKind::GF(f)),
            TyKind::Bundle(tys) => {
                c.ty_bundle_iter(tys.iter().map(|ty| ty.transfer(c)))
            },
            TyKind::RawBits => c.ty(TyKind::RawBits),
        }
    }

    /// Compute the number of bignum digits required to represent this type as `Bits`.  The total
    /// size in bits is `self.digits() * Bits::DIGIT_BITS`.
    pub fn digits(&self) -> usize {
        match *self {
            TyKind::Int(sz) |
            TyKind::Uint(sz) => {
                (sz.bits() as usize + Bits::DIGIT_BITS - 1) / Bits::DIGIT_BITS
            },
            TyKind::GF(f) => {
                (f.bit_size().bits() as usize + Bits::DIGIT_BITS - 1) / Bits::DIGIT_BITS
            },
            TyKind::Bundle(tys) => {
                tys.iter().map(|ty| ty.digits()).sum()
            },
            TyKind::RawBits => panic!("RawBits type has unknown digit width"),
        }
    }
}

impl<'a, 'b> Migrate<'a, 'b> for TyKind<'a> {
    type Output = TyKind<'b>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> TyKind<'b> {
        use self::TyKind::*;
        match self {
            Int(sz) => Int(sz),
            Uint(sz) => Uint(sz),
            GF(f) => GF(f),
            Bundle(tys) => {
                let tys = tys.iter().map(|&ty| v.visit(ty)).collect::<Vec<_>>();
                Bundle(v.new_circuit().intern_ty_list(&tys))
            },
            RawBits => RawBits,
        }
    }
}

static COMMON_TY_BOOL: TyKind = TyKind::BOOL;
static COMMON_TY_U8: TyKind = TyKind::U8;
static COMMON_TY_U16: TyKind = TyKind::U16;
static COMMON_TY_U32: TyKind = TyKind::U32;
static COMMON_TY_U64: TyKind = TyKind::U64;
static COMMON_TY_I8: TyKind = TyKind::I8;
static COMMON_TY_I16: TyKind = TyKind::I16;
static COMMON_TY_I32: TyKind = TyKind::I32;
static COMMON_TY_I64: TyKind = TyKind::I64;
static COMMON_TY_RAW_BITS: TyKind = TyKind::RawBits;

static COMMON_TYPES: &[&TyKind] = &[
    &COMMON_TY_BOOL,
    &COMMON_TY_U8,
    &COMMON_TY_U16,
    &COMMON_TY_U32,
    &COMMON_TY_U64,
    &COMMON_TY_I8,
    &COMMON_TY_I16,
    &COMMON_TY_I32,
    &COMMON_TY_I64,
    &COMMON_TY_RAW_BITS,
];

impl Ty<'_> {
    pub fn bool<'a>() -> Ty<'a> {
        Ty(&COMMON_TY_BOOL)
    }

    pub fn uint<'a>(width: usize) -> Ty<'a> {
        match width {
            8 => Ty(&COMMON_TY_U8),
            16 => Ty(&COMMON_TY_U16),
            32 => Ty(&COMMON_TY_U32),
            64 => Ty(&COMMON_TY_U64),
            _ => panic!("not a common bit width: {}", width),
        }
    }

    pub fn int<'a>(width: usize) -> Ty<'a> {
        match width {
            8 => Ty(&COMMON_TY_I8),
            16 => Ty(&COMMON_TY_I16),
            32 => Ty(&COMMON_TY_I32),
            64 => Ty(&COMMON_TY_I64),
            _ => panic!("not a common bit width: {}", width),
        }
    }

    pub fn raw_bits<'a>() -> Ty<'a> {
        Ty(&COMMON_TY_RAW_BITS)
    }
}


/// Wrapper for a `T` which ignores the wrapped value for equality and hashing purposes.  Comparing
/// two `Unhashed<T>`s always reports that they are equal, and hashing an `Unhashed<T>` has no
/// effect on the hasher state.  `Unhashed<Cell<T>>` is useful for cache fields that should be
/// ignored when the containing struct is inserted into a `HashMap` or `HashSet`.
#[derive(Clone, Copy, Debug, Default)]
pub struct Unhashed<T>(pub T);

impl<T> PartialEq for Unhashed<T> {
    fn eq(&self, _other: &Self) -> bool { true }
    fn ne(&self, _other: &Self) -> bool { false }
}

impl<T> Eq for Unhashed<T> {}

impl<T> Hash for Unhashed<T> {
    fn hash<H: Hasher>(&self, _state: &mut H) {
        // No-op
    }
}

impl<T> Deref for Unhashed<T> {
    type Target = T;
    fn deref(&self) -> &T { &self.0 }
}

impl<T> DerefMut for Unhashed<T> {
    fn deref_mut(&mut self) -> &mut T { &mut self.0 }
}

impl<'a, 'b, T: Migrate<'a, 'b>> Migrate<'a, 'b> for Unhashed<T> {
    type Output = Unhashed<T::Output>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Unhashed<T::Output> {
        Unhashed(v.visit(self.0))
    }
}


#[derive(Clone, Copy, PartialEq, Eq, Debug, Migrate)]
pub enum GateValue<'a> {
    /// The gate hasn't been evaluated yet.
    Unset,
    /// The gate evaluated to this value, using only public information.
    Public(Bits<'a>),
    /// The gate evaluated to this value, but its value depends on a secret input.
    Secret(Bits<'a>),
    /// The gate can't be evaluated until the value of this `Secret` is set.
    NeedsSecret(Secret<'a>),
    /// Evaluation of the gate failed unrecoverably.
    Failed,
}

impl<'a> Default for GateValue<'a> {
    fn default() -> GateValue<'a> { GateValue::Unset }
}

impl<'a> GateValue<'a> {
    pub fn from_bits(bits: Bits<'a>, secret: bool) -> GateValue<'a> {
        if secret {
            GateValue::Secret(bits)
        } else {
            GateValue::Public(bits)
        }
    }
}


#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PackedGateValue<'a> {
    inner: (usize, usize),
    _marker: PhantomData<GateValue<'a>>,
}

impl<'a> PackedGateValue<'a> {
    pub fn unpack(self) -> GateValue<'a> {
        unsafe {
            match self.inner {
                (0, 0) => GateValue::Unset,
                (0, 1) => GateValue::Failed,
                (0, secret) => GateValue::NeedsSecret(mem::transmute(secret)),
                (x, len) => {
                    let ptr = x & !1;
                    let is_secret = x & 1 != 0;
                    let bits = slice::from_raw_parts(ptr as *const _, len);
                    if is_secret {
                        GateValue::Secret(Bits(bits))
                    } else {
                        GateValue::Public(Bits(bits))
                    }
                },
            }
        }
    }
}

impl<'a> GateValue<'a> {
    pub fn pack(self) -> PackedGateValue<'a> {
        unsafe {
            let inner = match self {
                GateValue::Unset => (0, 0),
                GateValue::Failed => (0, 1),
                GateValue::NeedsSecret(s) => {
                    let y = mem::transmute(s);
                    assert!(y != 0 && y != 1);
                    (0, y)
                },
                GateValue::Public(bits) => {
                    let ptr = bits.0.as_ptr() as usize;
                    assert!(ptr != 0 && ptr & 1 == 0);
                    let x = ptr;
                    let y = bits.0.len();
                    (x, y)
                },
                GateValue::Secret(bits) => {
                    let ptr = bits.0.as_ptr() as usize;
                    assert!(ptr != 0 && ptr & 1 == 0);
                    let x = ptr | 1;
                    let y = bits.0.len();
                    (x, y)
                },
            };
            PackedGateValue { inner, _marker: PhantomData }
        }
    }
}

impl<'a> Default for PackedGateValue<'a> {
    fn default() -> PackedGateValue<'a> { GateValue::default().pack() }
}

impl<'a> fmt::Debug for PackedGateValue<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.unpack(), f)
    }
}

impl<'a, 'b> Migrate<'a, 'b> for PackedGateValue<'a> {
    type Output = PackedGateValue<'b>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> PackedGateValue<'b> {
        self.unpack().migrate(v).pack()
    }
}


#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Gate<'a> {
    /// Cached output type of this gate.  Computed when the `Gate` is created.  The result is
    /// stored here so that `GateKind::ty` runs in constant time, rather than potentially having
    /// recurse over the entire depth of the circuit.
    pub ty: Ty<'a>,
    pub kind: GateKind<'a>,
    pub label: Label<'a>,
    /// Hook function to run after successfully evaluating this gate.
    ///
    /// As the closure used here may contain `Wire<'a>` captures, it can't be migrated.  Migrate
    /// operations will instead clear this field; after migration, `eval_hook` will always be
    /// `None`.
    ///
    /// Note this field is ignored during interning.  This could result in confusing interactions
    /// where two `Gate`s unexpectedly alias and setting one gate's `eval_hook` overwrites the
    /// `eval_hook` that was provided for the other gate.  However, these hooks are only used for
    /// debugging, so this is okay for now.
    pub eval_hook: Unhashed<Cell<Option<EvalHookFn<'a>>>>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum GateKind<'a> {
    /// A literal/constant value.
    Lit(Bits<'a>, Ty<'a>),
    /// Retrieve a secret value from the witness.
    Secret(Secret<'a>),
    /// A gate that has been erased from the in-memory representation of the circuit.
    Erased(Erased<'a>),
    /// A function argument.  This gate kind should only appear inside function bodies.  `Argument`
    /// gates are created by the function-definition machinery; they should not be created
    /// manually.
    Argument(usize, Ty<'a>),
    /// Compute a unary operation.  All `UnOp`s have type `T -> T`.
    Unary(UnOp, Wire<'a>),
    /// Compute a binary operation.  All `BinOp`s have type `T -> T -> T`
    Binary(BinOp, Wire<'a>, Wire<'a>),
    /// Compute a binary operation.  All `BinOp`s have type `T -> u8 -> T`
    Shift(ShiftOp, Wire<'a>, Wire<'a>),
    /// Compute a comparison operation.  All `CmpOp`s have type `T -> T -> bool`.
    Compare(CmpOp, Wire<'a>, Wire<'a>),
    /// `Mux(cond, then_, else)`: depending on `cond`, select either `then_` or `else`.
    Mux(Wire<'a>, Wire<'a>, Wire<'a>),
    /// Convert a value to a different type.
    Cast(Wire<'a>, Ty<'a>),
    /// Pack several values into a bundle.
    Pack(&'a [Wire<'a>]),
    /// Extract one value from a bundle.
    Extract(Wire<'a>, usize),
    /// A custom gadget.
    // TODO: move fields to a struct (this variant is 5 words long)
    Gadget(GadgetKindRef<'a>, &'a [Wire<'a>]),
    /// A function call.  The wires are the arguments to the function.  Secret inputs to the
    /// function are provided as a list of pairs, giving a value for each `SecretInputId` used in
    /// the function.  (This would be a `HashMap`, but `Gate` is arena-allocated and thus never
    /// gets dropped, so putting a `HashMap` here would leak memory.)
    Call(Function<'a>, &'a [Wire<'a>], &'a [(SecretInputId, Secret<'a>)]),
}

impl<'a> Gate<'a> {
    pub fn is_lit(&self) -> bool {
        self.kind.is_lit()
    }
}

impl<'a> GateKind<'a> {
    pub fn ty(&self, c: &impl CircuitTrait<'a>) -> Ty<'a> {
        match *self {
            GateKind::Lit(_, ty) => ty,
            GateKind::Secret(s) => s.ty,
            GateKind::Erased(e) => e.ty,
            GateKind::Argument(_, ty) => ty,
            GateKind::Unary(_, w) => w.ty,
            GateKind::Binary(_, w, _) => w.ty,
            GateKind::Shift(_, w, _) => w.ty,
            GateKind::Compare(_, _, _) => c.ty(TyKind::BOOL),
            GateKind::Mux(_, w, _) => w.ty,
            GateKind::Cast(_, ty) => ty,
            GateKind::Pack(ws) => c.ty_bundle_iter(ws.iter().map(|&w| w.ty)),
            GateKind::Extract(w, i) => match *w.ty {
                TyKind::Bundle(tys) => tys[i],
                _ => panic!("invalid wire type {:?} in Extract", w.ty),
            },
            GateKind::Gadget(k, ws) => {
                let tys = ws.iter().map(|w| w.ty).collect::<Vec<_>>();
                k.typecheck(c.as_base(), &tys)
            },
            GateKind::Call(f, _, _) => f.result_wire.ty,
        }
    }

    pub fn is_lit(&self) -> bool {
        match *self {
            GateKind::Lit(..) => true,
            _ => false,
        }
    }

    pub fn as_secret(&self) -> Secret<'a> {
        match *self {
            GateKind::Secret(s) => s,
            _ => panic!("expected GateKind::Secret"),
        }
    }

    pub fn as_lit(&self) -> (Ty<'a>, Bits<'a>) {
        match *self {
            GateKind::Lit(b, t) => (t, b),
            _ => panic!("expected GateKind::Lit"),
        }
    }

    pub fn variant_name(&self) -> &str {
        use BinOp::*;
        use CmpOp::*;
        use GateKind::*;
        use UnOp::*;
        match self {
            Lit(_, _) => "Lit",
            Secret(_) => "Secret",
            Erased(_) => "Erased",
            Argument(_, _) => "Argument",
            Unary(op, _) => match op {
                Not => "Not",
                Neg => "Neg",
            },
            Binary(op, _, _) => match op {
                Add => "Add",
                Sub => "Sub",
                Mul => "Mul",
                Div => "Div",
                Mod => "Mod",
                And => "And",
                Or => "Or",
                Xor => "Xor",
            },
            Shift(_, _, _) => "Shift",
            Compare(op, _, _) => match op {
                Eq => "Eq",
                Ne => "Ne",
                Lt => "Lt",
                Le => "Le",
                Gt => "Gt",
                Ge => "Ge",
            },
            Mux(_, _, _) => "Mux",
            Cast(_, _) => "Cast",
            Pack(_) => "Pack",
            Extract(_, _) => "Extract",
            Gadget(_, _) => "Gadget",
            Call(_, _, _) => "Call",
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum BinOp {
    Add, Sub, Mul, Div, Mod,
    And, Or, Xor,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum ShiftOp {
    Shl, Shr,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum CmpOp {
    Eq, Ne, Lt, Le, Gt, Ge,
}

impl<'a, 'b> Migrate<'a, 'b> for Gate<'a> {
    type Output = Gate<'b>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Gate<'b> {
        Gate {
            ty: v.visit(self.ty),
            kind: v.visit(self.kind),
            label: v.visit(self.label),
            eval_hook: Unhashed(Cell::new(None)),
        }
    }
}

impl<'a, 'b> Migrate<'a, 'b> for GateKind<'a> {
    type Output = GateKind<'b>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> GateKind<'b> {
        use self::GateKind::*;
        match self {
            Lit(bits, ty) => Lit(v.visit(bits), v.visit(ty)),
            Secret(s) => Secret(v.visit(s)),
            Erased(e) => Erased(v.visit(e)),
            Argument(idx, ty) => Argument(idx, v.visit(ty)),
            Unary(op, a) => Unary(op, v.visit(a)),
            Binary(op, a, b) => Binary(op, v.visit(a), v.visit(b)),
            Shift(op, a, b) => Shift(op, v.visit(a), v.visit(b)),
            Compare(op, a, b) => Compare(op, v.visit(a), v.visit(b)),
            Mux(c, t, e) => Mux(v.visit(c), v.visit(t), v.visit(e)),
            Cast(a, ty) => Cast(v.visit(a), v.visit(ty)),
            Pack(ws) => {
                let ws = ws.iter().map(|&w| v.visit(w)).collect::<Vec<_>>();
                Pack(v.new_circuit().intern_wire_list(&ws))
            },
            Extract(w, idx) => Extract(v.visit(w), idx),
            Gadget(gk, ws) => {
                let gk = gk.transfer(v.new_circuit());
                let ws = ws.iter().map(|&w| v.visit(w)).collect::<Vec<_>>();
                let ws = v.new_circuit().intern_wire_list(&ws);
                Gadget(gk, ws)
            },
            Call(f, ws, ss) => {
                let f = v.visit(f);
                let ws = ws.iter().map(|&w| v.visit(w)).collect::<Vec<_>>();
                let ws = v.new_circuit().intern_wire_list(&ws);
                let ss = ss.iter().map(|&s| v.visit(s)).collect::<Vec<_>>();
                let ss = v.new_circuit().arena().alloc_slice_copy(&ss);
                Call(f, ws, ss)
            },
        }
    }
}


/// Declare a wrapper around an immutable reference, with `Eq` and `Hash` instances that compare by
/// address instead of by value.
macro_rules! declare_interned_pointer {
    ($(#[$attr:meta])* $pub_:vis struct $Ptr:ident <$lt:lifetime> => $T:ty;) => {
        $(#[$attr])*
        #[derive(Clone, Copy)]
        $pub_ struct $Ptr<$lt>(pub &$lt $T);

        impl<$lt> $Ptr<$lt> {
            pub fn as_ptr(self) -> *const $T {
                self.0 as *const $T
            }
        }

        impl<$lt> PartialEq for $Ptr<$lt> {
            fn eq(&self, other: &$Ptr<$lt>) -> bool {
                self.0 as *const _ == other.0 as *const _
            }

            fn ne(&self, other: &$Ptr<$lt>) -> bool {
                self.0 as *const _ != other.0 as *const _
            }
        }

        impl Eq for $Ptr<'_> {}

        impl<$lt> PartialOrd for $Ptr<$lt> {
            fn partial_cmp(&self, other: &$Ptr<$lt>) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        impl<$lt> Ord for $Ptr<$lt> {
            fn cmp(&self, other: &$Ptr<$lt>) -> Ordering {
                self.as_ptr().cmp(&other.as_ptr())
            }
        }

        impl<$lt> Hash for $Ptr<$lt> {
            fn hash<H: Hasher>(&self, state: &mut H) {
                (self.0 as *const $T).hash(state)
            }
        }

        impl<$lt> Deref for $Ptr<$lt> {
            type Target = $T;
            fn deref(&self) -> &$T {
                self.0
            }
        }

        impl<$lt> fmt::Pointer for $Ptr<$lt> {
            fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
                fmt::Pointer::fmt(&self.as_ptr(), fmt)
            }
        }
    };
}

declare_interned_pointer! {
    /// The output of a `Gate`, which carries a value during circuit evaluation.
    pub struct Wire<'a> => Gate<'a>;
}

impl<'a, 'b> Migrate<'a, 'b> for Wire<'a> {
    type Output = Wire<'b>;

    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Wire<'b> {
        v.visit_wire(self)
    }
}

thread_local! {
    static WIRE_DEBUG_DEPTH: Cell<usize> = Cell::new(2);
}

impl<'a> fmt::Debug for Wire<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        WIRE_DEBUG_DEPTH.with(|depth_cell| {
            let depth = depth_cell.get();
            if depth > 0 {
                depth_cell.set(depth - 1);
                let r = write!(fmt, "Wire({:p} => {:?})", self.0, self.0);
                depth_cell.set(depth);
                r
            } else {
                write!(fmt, "Wire({:p})", self.0)
            }
        })
    }
}

pub struct DebugDepth<T>(pub usize, pub T);

impl<T: fmt::Debug> fmt::Debug for DebugDepth<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        WIRE_DEBUG_DEPTH.with(|depth_cell| {
            let depth = depth_cell.get();
            depth_cell.set(self.0);
            let r = write!(fmt, "{:?}", self.1);
            depth_cell.set(depth);
            r
        })
    }
}


declare_interned_pointer! {
    /// A slot in the witness, which contains a secret value.
    ///
    /// For maximum flexibility in constructing and optimizing abstract circuits, the full witness
    /// is never represented explicitly.  Instead, individual `Secret`s can be created at any point
    /// and used or discarded as needed.  During lowering to a concrete circuit, each `Secret` in
    /// use within the circuit is added to the witness in an arbitrary order.
    ///
    /// With the addition of call gates, we consider each stack frame to have a separate witness.
    /// Each `Secret` used in a function body refers to an element of the witness for the current
    /// stack frame, identified by the `SecretInputId` stored in the `SecretValue::FunctionInput`.
    /// The `FunctionDef` contains a list of `SecretInputId`s that must be given values at each
    /// call, and `GateKind::Call` contains a list mapping `SecretInputId`s to `Secret`s in the
    /// caller's scope.
    #[derive(Debug)]
    pub struct Secret<'a> => SecretData<'a>;
}

impl<'a, 'b> Migrate<'a, 'b> for Secret<'a> {
    type Output = Secret<'b>;

    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Secret<'b> {
        v.visit_secret(self)
    }
}

/// The ID of a secret input to a function.  This is essentially used as an "argument name" when
/// passing secret values to functions: the `FunctionDef` declares a type for each `SecretInputId`
/// that it uses, and the caller must provide a value for each `SecretInputId` when it makes the
/// call.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Migrate)]
pub struct SecretInputId(pub usize);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Migrate)]
pub enum SecretValue<'a> {
    /// The circuit is in prover mode, and the value is initialized.
    ProverInit(Bits<'a>),
    /// The circuit is in prover mode, and the value hasn't be initialized yet.
    ProverUninit,
    /// The circuit is in verifier mode, so the value will never be initialized.
    VerifierUnknown,
    /// This secret is inside a function, and its value is taken from one of the function's secret
    /// inputs.
    FunctionInput(SecretInputId),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PackedSecretValue<'a> {
    inner: (usize, usize),
    _marker: PhantomData<Bits<'a>>,
}

impl<'a> SecretValue<'a> {
    /// Produce either `ProverUninit` or `VerifierUnknown`, depending on the value of `is_prover`.
    pub fn uninit(is_prover: bool) -> SecretValue<'a> {
        if is_prover {
            SecretValue::ProverUninit
        } else {
            SecretValue::VerifierUnknown
        }
    }

    /// Produce either `ProverInit(mk_val())` or `VerifierUnknown`, depending on the value of
    /// `is_prover`.
    pub fn init(is_prover: bool, mk_val: impl FnOnce() -> Bits<'a>) -> SecretValue<'a> {
        if is_prover {
            SecretValue::ProverInit(mk_val())
        } else {
            SecretValue::VerifierUnknown
        }
    }

    pub fn pack(self) -> PackedSecretValue<'a> {
        let inner = match self {
            SecretValue::ProverInit(bits) => {
                let ptr = bits.0.as_ptr() as usize;
                assert!(ptr >= 2);
                let len = bits.0.len();
                (ptr, len)
            },
            SecretValue::ProverUninit => (0, 0),
            SecretValue::VerifierUnknown => (0, 1),
            SecretValue::FunctionInput(i) => (1, i.0),
        };
        PackedSecretValue { inner, _marker: PhantomData }
    }
}

impl<'a> PackedSecretValue<'a> {
    pub fn unpack(self) -> SecretValue<'a> {
        unsafe {
            match self.inner {
                (0, 0) => SecretValue::ProverUninit,
                (0, 1) => SecretValue::VerifierUnknown,
                (1, i) => SecretValue::FunctionInput(SecretInputId(i)),
                (ptr, len) => {
                    let bits = slice::from_raw_parts(ptr as *const _, len);
                    SecretValue::ProverInit(Bits(bits))
                }
            }
        }
    }
}

impl<'a> fmt::Debug for PackedSecretValue<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.unpack(), f)
    }
}

impl<'a, 'b> Migrate<'a, 'b> for PackedSecretValue<'a> {
    type Output = PackedSecretValue<'b>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> PackedSecretValue<'b> {
        self.unpack().migrate(v).pack()
    }
}


/// Wrapper that signals that the wrapped type implements `Copy`.  Coercing `&IsCopy<Concrete>` to
/// `&IsCopy<dyn Trait>` retains the fact that the underlying concrete type of the `dyn Trait`
/// implements `Copy`.
#[repr(transparent)]
struct IsCopy<T: ?Sized>(T);

impl<T: ?Sized> IsCopy<T> {
    pub fn new_ref<'a>(r: &'a T) -> &'a IsCopy<T>
    where T: Copy {
        unsafe { mem::transmute(r) }
    }

    pub fn get_ref(&self) -> &T {
        &self.0
    }
}

/// `Migrate`-able wrapper for references to arena-allocated trait objects.  Requires `T: 'static`,
/// meaning that the trait object can simply be copied to the new arena without requiring any
/// migrations within its data.
struct ArenaDyn<'a, T: ?Sized>(&'a IsCopy<T>);

impl<'a, T: ?Sized> Clone for ArenaDyn<'a, T> {
    fn clone(&self) -> Self { *self }
}

impl<'a, T: ?Sized> Copy for ArenaDyn<'a, T> {}

impl<'a, T: ?Sized> ArenaDyn<'a, T> {
    /// Create a new `ArenaDyn` reference.  We use `IsCopy` to assert that the concrete type
    /// underlying `T` is `Copy`.  We can't add `T: Copy` since that won't hold when `T` is a `dyn`
    /// type.
    pub fn new(r: &'a IsCopy<T>) -> ArenaDyn<'a, T>
    where T: 'static {
        ArenaDyn(r)
    }
}

impl<'a, T: ?Sized> fmt::Debug for ArenaDyn<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ArenaDyn({})", any::type_name::<T>())
    }
}

impl<'a, 'b, T: ?Sized + 'static> Migrate<'a, 'b> for ArenaDyn<'a, T> {
    type Output = ArenaDyn<'b, T>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> ArenaDyn<'b, T> {
        // Copy the unsized value.
        unsafe {
            let size = mem::size_of_val::<IsCopy<T>>(self.0);
            let align = mem::align_of_val::<IsCopy<T>>(self.0);
            let layout = Layout::from_size_align(size, align).unwrap();
            let src_ptr = self.0 as *const IsCopy<T> as *const u8;
            let dest_ptr = v.new_circuit().arena().alloc_layout(layout).as_ptr();
            ptr::copy_nonoverlapping(src_ptr, dest_ptr, size);

            // Keep the vtable, but change the address.  This is a bit of a hack, since things like
            // `ptr::from_raw_parts` are not yet stable.
            let mut t_ptr = self.0 as *const IsCopy<T>;
            *(&mut t_ptr as *mut *const IsCopy<T> as *mut *const u8) = dest_ptr;
            ArenaDyn(&*t_ptr)
        }
    }
}

impl<'a, T: ?Sized> Deref for ArenaDyn<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.0.get_ref()
    }
}


type SecretInitFn<'a> = ArenaDyn<'a,
    dyn for<'b> Fn(&CircuitBase<'b>, *const (), &[Bits<'b>]) -> Bits<'b> + 'static>;

#[derive(Clone, Debug)]
pub struct SecretData<'a> {
    pub ty: Ty<'a>,
    val: Cell<PackedSecretValue<'a>>,
    /// Indicates whether this `Secret` has been used to construct a gate.  Each `Secret` can only
    /// be used in one place in the circuit.  This flag is `false` on construction and becomes
    /// `true` at the first use; if it is used again after that, a panic occurs.  Note that
    /// constructing a second gate from the same `Secret` will panic even if the first gate isn't
    /// used anywhere.
    used: Cell<bool>,

    init: Option<SecretInitFn<'a>>,
    /// Dependencies for computing derived secrets.  The values on these wires (represented as
    /// `Bits`) will be passed to `init`.
    pub deps: &'a [Wire<'a>],
    secret_type: TypeId,
}

impl<'a, 'b> Migrate<'a, 'b> for SecretData<'a> {
    type Output = SecretData<'b>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> SecretData<'b> {
        let deps = self.deps.iter().map(|&w| v.visit(w)).collect::<Vec<_>>();
        let deps = v.new_circuit().intern_wire_list(&deps);
        SecretData {
            ty: v.visit(self.ty),
            val: v.visit(self.val),
            used: v.visit(self.used),
            init: v.visit(self.init),
            deps,
            secret_type: self.secret_type,
        }
    }
}

impl<'a> SecretData<'a> {
    fn new(ty: Ty<'a>, val: SecretValue<'a>) -> SecretData<'a> {
        SecretData {
            ty,
            val: Cell::new(val.pack()),
            used: Cell::new(false),
            init: None,
            deps: &[],
            secret_type: TypeId::of::<()>(),
        }
    }

    fn new_lazy_prover<S: 'static>(
        ty: Ty<'a>,
        init: SecretInitFn<'a>,
        deps: &'a [Wire<'a>],
    ) -> SecretData<'a> {
        SecretData {
            ty,
            val: Cell::new(SecretValue::ProverUninit.pack()),
            used: Cell::new(false),
            init: Some(init),
            deps,
            secret_type: TypeId::of::<S>(),
        }
    }

    pub fn secret_value(&self) -> SecretValue<'a> {
        self.val.get().unpack()
    }

    pub fn set_used(&self) {
        assert!(!self.used.get(), "this secret has already been used");
        self.used.set(true);
    }

    pub fn has_val(&self) -> bool {
        match self.val.get().unpack() {
            SecretValue::ProverInit(_) => true,
            SecretValue::ProverUninit => false,
            SecretValue::VerifierUnknown => false,
            SecretValue::FunctionInput(_) =>
                panic!("tried to access value of abstract function input"),
        }
    }

    pub fn set(&self, bits: Bits<'a>) {
        match self.val.get().unpack() {
            SecretValue::ProverInit(_) =>
                panic!("secret value has already been set"),
            SecretValue::ProverUninit => {
                self.val.set(SecretValue::ProverInit(bits).pack());
            },
            SecretValue::VerifierUnknown =>
                panic!("can't provide secret values when running in verifier mode"),
            SecretValue::FunctionInput(_) =>
                panic!("can't provide secret value for abstract function input"),
        }
    }

    pub fn set_default(&self, bits: Bits<'a>) {
        match self.val.get().unpack() {
            SecretValue::ProverInit(_) => {},
            SecretValue::ProverUninit => {
                self.val.set(SecretValue::ProverInit(bits).pack());
            },
            SecretValue::VerifierUnknown => {},
            SecretValue::FunctionInput(_) => {},
        }
    }

    pub fn set_from_lit(&self, w: Wire<'a>, force: bool) {
        let (ty, bits) = w.kind.as_lit();
        assert!(ty == self.ty, "type mismatch in secret init: {:?} != {:?}", ty, self.ty);
        if force {
            self.set(bits);
        } else {
            self.set_default(bits);
        }
    }

    pub fn has_init(&self) -> bool {
        self.init.is_some()
    }

    /// Run the lazy initialization function to calculate the value of this secret.
    ///
    /// Note that this does not call `self.set`.
    pub fn init(
        &self,
        c: &CircuitBase<'a>,
        secret: &dyn Any,
        dep_vals: &[Bits<'a>],
    ) -> Bits<'a> {
        assert!(self.secret_type == secret.type_id() || self.secret_type == TypeId::of::<()>());
        let init = self.init.unwrap();
        let bits = unsafe { init(c, secret as *const dyn Any as *const (), dep_vals) };
        bits
    }
}

/// A handle that can be used to set the value of a `Secret`.  Sets a default value on drop, if a
/// default was provided when the handle was constructed.
#[derive(Debug)]
pub struct SecretHandle<'a> {
    s: Secret<'a>,
    default: Bits<'a>,
}

impl<'a> SecretHandle<'a> {
    fn new(s: Secret<'a>, default: Bits<'a>) -> SecretHandle<'a> {
        SecretHandle { s, default }
    }

    pub fn set(&self, c: &impl CircuitTrait<'a>, val: impl AsBits) {
        let bits = c.bits(self.s.ty, val);
        self.s.set(bits);
    }

    /// Set the secret to its default value, if it hasn't been set yet.
    pub fn apply_default(&self) {
        self.s.set_default(self.default);
    }
}

impl<'a> Drop for SecretHandle<'a> {
    fn drop(&mut self) {
        self.apply_default();
    }
}

impl<'a, 'b> Migrate<'a, 'b> for SecretHandle<'a> {
    type Output = SecretHandle<'b>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> SecretHandle<'b> {
        let sh = ManuallyDrop::new(self);
        SecretHandle {
            s: v.visit(sh.s),
            default: v.visit(sh.default),
        }
    }
}


/// Wrapper around `CircuitBase<'a>`, where the secret type of the circuit is known to be `S`.
#[repr(transparent)]
pub struct CircuitBaseWithSecretType<'a, S> {
    c: CircuitBase<'a>,
    _marker: PhantomData<S>,
}

impl<'a, S> Deref for CircuitBaseWithSecretType<'a, S> {
    type Target = CircuitBase<'a>;
    fn deref(&self) -> &CircuitBase<'a> {
        &self.c
    }
}


#[derive(Clone, Debug, Migrate)]
pub struct ErasedData<'a> {
    pub ty: Ty<'a>,
    value: PackedGateValue<'a>,
}

impl<'a> ErasedData<'a> {
    pub fn new(ty: Ty<'a>, bits: Bits<'a>, secret: bool) -> ErasedData<'a> {
        ErasedData {
            ty,
            value: GateValue::from_bits(bits, secret).pack(),
        }
    }

    pub fn new_unset(ty: Ty<'a>) -> ErasedData<'a> {
        ErasedData {
            ty,
            value: GateValue::Unset.pack(),
        }
    }

    pub fn gate_value(&self) -> GateValue<'a> {
        self.value.unpack()
    }

    pub fn bits(&self) -> Bits<'a> {
        match self.value.unpack() {
            GateValue::Public(bits) => bits,
            GateValue::Secret(bits) => bits,
            _ => unreachable!(),
        }
    }

    pub fn is_secret(&self) -> bool {
        match self.value.unpack() {
            GateValue::Public(_) => false,
            GateValue::Secret(_) => true,
            _ => unreachable!(),
        }
    }
}

declare_interned_pointer! {
    /// A pointer to data about an erased wire.  Similar to `Secret`s, each `Erased` has a distinct
    /// identity.
    #[derive(Debug)]
    pub struct Erased<'a> => ErasedData<'a>;
}

impl<'a, 'b> Migrate<'a, 'b> for Erased<'a> {
    type Output = Erased<'b>;

    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Erased<'b> {
        v.visit_erased(self)
    }
}


#[derive(Clone, Copy)]
pub struct EvalHookFn<'a>(pub &'a (dyn Fn(
    &CircuitBase<'a>,
    &mut dyn eval::EvaluatorObj<'a>,
    Wire<'a>,
    Bits<'a>,
) + 'a));

impl fmt::Debug for EvalHookFn<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "EvalHookFn(..)")
    }
}



declare_interned_pointer! {
    #[derive(Debug)]
    pub struct Ty<'a> => TyKind<'a>;
}

impl<'a, 'b> Migrate<'a, 'b> for Ty<'a> {
    type Output = Ty<'b>;

    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Ty<'b> {
        let kind = v.visit(*self);
        Ty(v.new_circuit().intern_ty(kind))
    }
}


pub unsafe trait GadgetKindSupport<'a> {
    fn type_name(&self) -> &'static str;
    fn eq_dyn(&self, other: &dyn GadgetKind<'a>) -> bool;
    fn hash_dyn(&self, state: &mut dyn Hasher);
    /// Clone `self` into `*dest`.  `dest` must be properly aligned.
    unsafe fn clone_dyn(&self, dest: *mut u8);
    /// Create a new `&dyn GadgetKindSupport` with the same type as `self` but a different data
    /// pointer.
    unsafe fn make_dyn(&self, data: *const u8) -> *const dyn GadgetKind<'a>;
}

macro_rules! impl_gadget_kind_support {
    (<$lt:lifetime> $T:ty) => {
        unsafe impl<$lt> $crate::ir::circuit::GadgetKindSupport<$lt> for $T {
            fn type_name(&self) -> &'static str { std::any::type_name::<$T>() }

            fn eq_dyn(&self, other: &dyn $crate::ir::circuit::GadgetKind<'a>) -> bool {
                unsafe {
                    let other = match $crate::ir::circuit::downcast_gadget_kind(other) {
                        Some(x) => x,
                        None => return false,
                    };
                    self == other
                }
            }

            fn hash_dyn(&self, mut state: &mut dyn core::hash::Hasher) {
                // Hash the type name first.  Otherwise all empty structs would have the same hash.
                core::hash::Hash::hash(self.type_name(), &mut state);
                core::hash::Hash::hash(self, &mut state);
            }

            unsafe fn clone_dyn(&self, dest: *mut u8) {
                (dest as *mut Self).write(core::clone::Clone::clone(self))
            }

            unsafe fn make_dyn(&self, data: *const u8) -> *const dyn GadgetKind<'a> {
                &*(data as *const Self)
            }
        }
    };

    ($T:ty) => { impl_gadget_kind_support! { <'a> $T } }
}

/// Defines a kind of gadget.  Instances of a gadget can be added to a `Circuit` using
/// `define_gadget_kind` and the `Circuit::gadget` constructor.
pub trait GadgetKind<'a>: GadgetKindSupport<'a> + 'a {
    /// Intern this `GadgetKind` into a new `Circuit`.  This should usually be implemented as
    ///
    /// ```Rust,ignore
    /// fn transfer<'b>(&self, c: &Circuit<'b>) -> GadgetKindRef<'b> {
    ///     c.intern_gadget_kind(self.clone())
    /// }
    /// ```
    ///
    /// However, this can't be provided automatically because it requires `Self: Clone + 'static`.
    /// The `Clone` bound implies `Sized`, which would make this trait non-object-safe, and
    /// `'static` means the `GadgetKind` can't contain any `Ty<'a>` values.
    fn transfer<'b>(&self, c: &CircuitBase<'b>) -> GadgetKindRef<'b>;

    /// Validate the argument types for an instance of this kind of gadget.  Returns the output
    /// type of a gadget.
    fn typecheck(&self, c: &CircuitBase<'a>, arg_tys: &[Ty<'a>]) -> Ty<'a>;

    /// Decompose this gadget into primitive gates.  This may be called if the backend doesn't
    /// support this gadget.
    fn decompose(
        &self,
        c: DynCircuitRef<'a, '_>,
        args: &[Wire<'a>],
    ) -> Wire<'a>;

    /// Evaluate this gadget on the provided inputs.
    fn eval(&self, arg_tys: &[Ty<'a>], args: &[eval::EvalResult<'a>]) -> eval::EvalResult<'a>;
}

declare_interned_pointer! {
    pub struct GadgetKindRef<'a> => dyn GadgetKind<'a>;
}

impl<'a> GadgetKindRef<'a> {
    pub fn name(self) -> &'static str {
        self.type_name().split("::").last().unwrap_or("")
    }

    // TODO: there's probably some way to break memory safety with this, exploiting
    // co/contravariance of lifetimes
    pub fn cast<T: GadgetKind<'a>>(self) -> Option<&'a T> {
        unsafe { downcast_gadget_kind(self.0) }
    }

    pub fn is<T: GadgetKind<'a>>(self) -> bool {
        self.cast::<T>().is_some()
    }
}

impl<'a> fmt::Debug for GadgetKindRef<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "GadgetKindRef({})", self.name())
    }
}

pub unsafe fn downcast_gadget_kind<'a, 'b, T: GadgetKind<'a>>(
    gk: &'b dyn GadgetKind<'a>,
) -> Option<&'b T> {
    if gk.type_name() != any::type_name::<T>() {
        None
    } else {
        Some(mem::transmute(gk as *const _ as *const u8))
    }
}


/// Helper type for making `dyn GadgetKind` hashable, so it can be stored in the `Circuit`'s
/// interning tables.
#[repr(transparent)]
struct HashDynGadgetKind<'a>(dyn GadgetKind<'a>);

impl<'a> HashDynGadgetKind<'a> {
    pub fn new<'b>(gk: &'b dyn GadgetKind<'a>) -> &'b HashDynGadgetKind<'a> {
        unsafe { mem::transmute(gk) }
    }
}

impl PartialEq for HashDynGadgetKind<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq_dyn(&other.0)
    }
}

impl Eq for HashDynGadgetKind<'_> {}

impl Hash for HashDynGadgetKind<'_> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.0.hash_dyn(h)
    }
}


#[derive(Clone, Debug)]
pub struct FunctionDef<'a> {
    pub name: &'a str,
    /// The argument types of this function.  If the function body contains an `Argument(i)` gate,
    /// the type of that gate is `arg_tys[i]`.
    pub arg_tys: &'a [Ty<'a>],
    /// The secret inputs required by this function.  Each `Call` to this function must provide a
    /// `Secret` of the indicated `Ty` for each `SecretInputId` in this list.
    pub secret_inputs: &'a [(SecretInputId, Ty<'a>)],
    /// The output of the function body.  This will typically depend in some way on the function's
    /// `Argument` gates.  For functions that need to return multiple values, this wire can have a
    /// `Bundle` type.
    pub result_wire: Wire<'a>,
}

impl<'a, 'b> Migrate<'a, 'b> for FunctionDef<'a> {
    type Output = FunctionDef<'b>;

    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> FunctionDef<'b> {
        let arg_tys = self.arg_tys.iter().map(|&ty| v.visit(ty)).collect::<Vec<_>>();
        let secret_inputs = self.secret_inputs.iter().map(|&ty| v.visit(ty)).collect::<Vec<_>>();
        FunctionDef {
            name: v.new_circuit().intern_str(self.name),
            arg_tys: v.new_circuit().intern_ty_list(&arg_tys),
            secret_inputs: v.new_circuit().arena().alloc_slice_copy(&secret_inputs),
            result_wire: v.visit(self.result_wire),
        }
    }
}

declare_interned_pointer! {
    #[derive(Debug)]
    pub struct Function<'a> => FunctionDef<'a>;
}

impl<'a, 'b> Migrate<'a, 'b> for Function<'a> {
    type Output = Function<'b>;

    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Function<'b> {
        v.visit_function(self)
    }
}


pub struct CellResetGuard<'a, T> {
    cell: &'a Cell<T>,
    old: Cell<T>,
}

impl<'a, T> CellResetGuard<'a, T> {
    /// Set the contents of `cell` to `new`, and return a guard that restores the previous value
    /// when dropped.
    pub fn new(cell: &'a Cell<T>, new: T) -> CellResetGuard<'a, T> {
        let old = Cell::new(new);
        // We use `swap` to avoid copying the new or old value.
        cell.swap(&old);
        CellResetGuard { cell, old }
    }
}

impl<'a, T> Drop for CellResetGuard<'a, T> {
    fn drop(&mut self) {
        self.cell.swap(&self.old)
    }
}


declare_interned_pointer! {
    #[derive(Debug)]
    pub struct Label<'a> => str;
}

impl fmt::Display for Label<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str(self.0)
    }
}

impl<'a, 'b> Migrate<'a, 'b> for Label<'a> {
    type Output = Label<'b>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Label<'b> {
        Label(v.new_circuit().intern_str(self.0))
    }
}


/// An arbitrary-sized array of bits.  Used to represent values in the circuit and
/// evaluator.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Bits<'a>(pub &'a [u32]);

impl<'a> Bits<'a> {
    pub const DIGIT_BITS: usize = 32;

    pub fn width(&self) -> u16 {
        for (i, &x) in self.0.iter().enumerate().rev() {
            if x != 0 {
                let b = (i + 1) * 32 - x.leading_zeros() as usize;
                return u16::try_from(b).unwrap();
            }
        }
        0
    }

    pub fn as_u64(&self) -> Option<u64> {
        match self.0.len() {
            0 => Some(0),
            1 => Some(self.0[0] as u64),
            2 => Some(self.0[0] as u64 | (self.0[1] as u64) << 32),
            _ => None,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.0.iter().all(|&x| x == 0)
    }

    pub fn to_biguint(&self) -> BigUint {
        BigUint::from_slice(self.0)
    }

    /// Interpret these bits as an integer of type `ty`.  For `TyKind::Uint(sz)`, the result is in
    /// the range `0 .. 2^sz`; for `TyKind::Int(sz)`, it's in the range `-2^(sz-1) .. 2^(sz-1)`.
    pub fn to_bigint(&self, ty: Ty) -> BigInt {
        match *ty {
            TyKind::Uint(sz) => {
                assert!(self.width() <= sz.bits());
                BigInt::from_biguint(Sign::Plus, BigUint::from_slice(self.0))
            },
            TyKind::Int(sz) => {
                assert!(self.width() <= sz.bits());
                let mut i = BigInt::from_biguint(Sign::Plus, BigUint::from_slice(self.0));
                let sign_bit = sz.bits() as usize - 1;
                let sb_idx = sign_bit / 32;
                let sb_off = sign_bit % 32;
                let neg = self.0.get(sb_idx).cloned().unwrap_or(0) >> sb_off != 0;
                if neg {
                    // For signed integers, the high bit has value `-2^(N-1)` instead of `2^(N-1)`.
                    // So when the high bit is set, the value of `i` needs an adjustment of `-2^N`
                    // to go from unsigned to signed interpretation.
                    i -= BigInt::from(1) << sz.bits();
                }
                i
            },
            _ => panic!("expected an integer type, but got {:?}", ty),
        }
    }

    pub fn get(&self, i: usize) -> bool {
        let idx = i / Self::DIGIT_BITS;
        let off = i % Self::DIGIT_BITS;
        let digit = self.0.get(idx).cloned().unwrap_or(0);
        (digit >> off) & 1 != 0
    }

    pub fn zero() -> Bits<'a> {
        Bits(&COMMON_BITS_ZERO)
    }

    pub fn one() -> Bits<'a> {
        Bits(&COMMON_BITS_ONE)
    }
}

impl<'a, 'b> Migrate<'a, 'b> for Bits<'a> {
    type Output = Bits<'b>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Bits<'b> {
        v.new_circuit().intern_bits(self.0)
    }
}

static COMMON_BITS_ZERO: [u32; 1] = [0];
static COMMON_BITS_ONE: [u32; 1] = [1];

static COMMON_BITS: &[&[u32]] = &[
    &COMMON_BITS_ZERO,
    &COMMON_BITS_ONE,
];

pub trait AsBits {
    /// Convert `self` to `Bits`, interned in circuit `c`.  `width` is the size of the output;
    /// signed integers should be sign-extended to this width before conversion.
    fn as_bits<'a>(&self, c: &CircuitBase<'a>, width: IntSize) -> Bits<'a>;
}

impl AsBits for Bits<'_> {
    fn as_bits<'a>(&self, c: &CircuitBase<'a>, _width: IntSize) -> Bits<'a> {
        c.intern_bits(self.0)
    }
}

impl AsBits for BigUint {
    fn as_bits<'a>(&self, c: &CircuitBase<'a>, _width: IntSize) -> Bits<'a> {
        c.intern_bits(&self.to_u32_digits())
    }
}

impl AsBits for bool {
    fn as_bits<'a>(&self, _c: &CircuitBase<'a>, width: IntSize) -> Bits<'a> {
        assert_eq!(width, IntSize(1));
        if *self { Bits::one() } else { Bits::zero() }
    }
}

impl AsBits for u8 {
    fn as_bits<'a>(&self, c: &CircuitBase<'a>, width: IntSize) -> Bits<'a> {
        (*self as u32).as_bits(c, width)
    }
}

impl AsBits for u16 {
    fn as_bits<'a>(&self, c: &CircuitBase<'a>, width: IntSize) -> Bits<'a> {
        (*self as u32).as_bits(c, width)
    }
}

impl AsBits for u32 {
    fn as_bits<'a>(&self, c: &CircuitBase<'a>, _width: IntSize) -> Bits<'a> {
        c.intern_bits(&[*self])
    }
}

impl AsBits for u64 {
    fn as_bits<'a>(&self, c: &CircuitBase<'a>, _width: IntSize) -> Bits<'a> {
        let lo = *self as u32;
        let hi = (*self >> 32) as u32;
        c.intern_bits(&[lo, hi])
    }
}

impl AsBits for BigInt {
    fn as_bits<'a>(&self, c: &CircuitBase<'a>, width: IntSize) -> Bits<'a> {
        let mask = (BigInt::from(1) << width.bits()) - 1;
        let (sign, val) = (self & &mask).into_parts();
        assert!(sign != Sign::Minus);
        val.as_bits(c, width)
    }
}

impl AsBits for &'_ BigInt {
    fn as_bits<'a>(&self, c: &CircuitBase<'a>, width: IntSize) -> Bits<'a> {
        (*self).as_bits(c, width)
    }
}

impl AsBits for i32 {
    fn as_bits<'a>(&self, c: &CircuitBase<'a>, width: IntSize) -> Bits<'a> {
        if width == IntSize(32) {
            (*self as u32).as_bits(c, width)
        } else {
            BigInt::from(*self).as_bits(c, width)
        }
    }
}

impl AsBits for i64 {
    fn as_bits<'a>(&self, c: &CircuitBase<'a>, width: IntSize) -> Bits<'a> {
        if width == IntSize(64) {
            (*self as u64).as_bits(c, width)
        } else {
            BigInt::from(*self).as_bits(c, width)
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct BitsToIntError {
    actual: u16,
    expected: u16,
}

impl fmt::Display for BitsToIntError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(
            fmt,
            "too many bits for target type: got {}, but expected at most {}",
            self.actual, self.expected,
        )
    }
}

impl TryFrom<Bits<'_>> for u32 {
    type Error = BitsToIntError;
    fn try_from(bits: Bits) -> Result<u32, BitsToIntError> {
        if bits.width() > 32 {
            return Err(BitsToIntError { actual: bits.width(), expected: 32 });
        }
        Ok(bits.0[0])
    }
}

impl TryFrom<Bits<'_>> for u64 {
    type Error = BitsToIntError;
    fn try_from(bits: Bits) -> Result<u64, BitsToIntError> {
        if bits.width() > 64 {
            return Err(BitsToIntError { actual: bits.width(), expected: 64 });
        }
        Ok(bits.0[0] as u64 | (bits.0[1] as u64) << 32)
    }
}
