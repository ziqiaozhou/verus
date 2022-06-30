use core::cell::UnsafeCell;
use core::mem::MaybeUninit;

#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::modes::*;

// TODO implement: borrow_mut; figure out Drop, see if we can avoid leaking?

/// `PCell<V>` (which stands for "permissioned call") is the primitive Verus `Cell` type.
///
/// Technically, it is a wrapper around
/// `core::cell::UnsafeCell<core::mem::MaybeUninit<V>>`, and thus has the same runtime
/// properties: there are no runtime checks (as there would be for Rust's traditional
/// [`core::cell::RefCell`](https://doc.rust-lang.org/std/cell/struct.RefCell.html)).
/// Its data may be uninitialized.
///
/// Furthermore (and unlike both
/// [`core::cell::Cell`](https://doc.rust-lang.org/std/cell/struct.Cell.html) and
/// [`core::cell::RefCell`](https://doc.rust-lang.org/std/cell/struct.RefCell.html)),
/// a `PCell<V>` may be `Sync` (depending on `V`).
/// Thanks to verification, Verus ensures that access to the cell is data-race-free.
///
/// `PCell` uses a _ghost permission token_ similar to [`ptr::PPtr`] -- see the [`ptr::PPtr`]
/// documentation for the basics.
/// For `PCell`, the associated type of the permission token is [`cell::Permission`].
///
/// ### Differences from `PPtr`.
///
/// The key difference is that, whereas [`ptr::PPtr`] represents a fixed address in memory,
/// a `PCell` has _no_ fixed address because a `PCell` might be moved.
/// As such, the [`pcell.id()`](PCell::id) does not correspond to a memory address; rather,
/// it is a unique identifier that is fixed for a given cell, even when it is moved.
///
/// The arbitrary ID given by [`pcell.id()`](PCell::id) is of type [`CellId`].
/// Despite the fact that it is, in some ways, "like a pointer", note that
/// `CellId` does not support any meangingful arithmetic,
/// has no concept of a "null ID",
/// and has no runtime representation.
///
/// Also note that the `PCell` might be dropped before the `Permission` token is dropped,
/// although in that case it will no longer be possible to use the `Permission` in `exec` code
/// to extract data from the cell.
///
/// ### Example (TODO)

#[verifier(external_body)]
pub struct PCell<#[verifier(strictly_positive)] V> {
    ucell: UnsafeCell<MaybeUninit<V>>,
}

// PCell is always safe to Send/Sync. It's the Permission object where Send/Sync matters.
// (It doesn't matter if you move the bytes to another thread if you can't access them.)

#[verifier(external)]
unsafe impl<T> Sync for PCell<T> {}

#[verifier(external)]
unsafe impl<T> Send for PCell<T> {}

// Permission<V>, on the other hand, needs to inherit both Send and Sync from the V,
// which it does by default in the given definition.
// (Note: this depends on the current behavior that #[spec] fields are still counted for marker traits)

#[proof]
#[verifier(unforgeable)]
pub struct Permission<V> {
    #[spec] pub pcell: CellId,
    #[spec] pub value: option::Option<V>,
}

#[verifier(external_body)]
pub struct CellId {
    id: int,
}

impl<V> PCell<V> {
    #[inline(always)]
    #[verifier(external_body)]
    pub fn empty() -> (PCell<V>, Proof<Permission<V>>) {
        ensures(|pt : (PCell<V>, Proof<Permission<V>>)|
            equal(pt.1, Proof(Permission{ pcell: pt.0.id(), value: option::Option::None }))
        );

        let p = PCell { ucell: UnsafeCell::new(MaybeUninit::uninit()) };
        let Proof(t) = exec_proof_from_false();
        (p, Proof(t))
    }

    // A unique ID for the cell.
    // This does not correspond to a pointer address
    // because the ID needs to stay the same even if the cell moves.
    fndecl!(pub fn id(&self) -> CellId);

    #[inline(always)]
    #[verifier(external_body)]
    pub fn put(&self, #[proof] perm: &mut Permission<V>, v: V) {
        requires([
            equal(self.id(), old(perm).pcell),
            equal(old(perm).value, option::Option::None),
        ]);
        ensures(
            equal(perm.pcell, old(perm).pcell) &&
            equal(perm.value, option::Option::Some(v))
        );
        opens_invariants_none();

        unsafe {
            *(self.ucell.get()) = MaybeUninit::new(v);
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn take(&self, #[proof] perm: &mut Permission<V>) -> V {
        requires([
            equal(self.id(), old(perm).pcell),
            old(perm).value.is_Some(),
        ]);
        ensures(|v: V| [
            equal(perm.pcell, old(perm).pcell),
            equal(perm.value, option::Option::None),
            equal(v, old(perm).value.get_Some_0()),
        ]);
        opens_invariants_none();

        unsafe {
            let mut m = MaybeUninit::uninit();
            core::mem::swap(&mut m, &mut *self.ucell.get());
            m.assume_init()
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn replace(&self, #[proof] perm: &mut Permission<V>, in_v: V) -> V {
        requires([
            equal(self.id(), old(perm).pcell),
            old(perm).value.is_Some(),
        ]);
        ensures(|out_v: V| [
            equal(perm.pcell, old(perm).pcell),
            equal(perm.value, option::Option::Some(in_v)),
            equal(out_v, old(perm).value.get_Some_0()),
        ]);
        opens_invariants_none();

        unsafe {
            let mut m = MaybeUninit::new(in_v);
            core::mem::swap(&mut m, &mut *self.ucell.get());
            m.assume_init()
        }
    }

    /// Note that `self` actually contains the data in its interior, so it needs
    /// to outlive the returned borrow.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn borrow<'a>(&'a self, #[proof] perm: &'a Permission<V>) -> &'a V {
        requires([
            equal(self.id(), perm.pcell),
            perm.value.is_Some(),
        ]);
        ensures(|v: V|
            equal(v, perm.value.get_Some_0())
        );
        opens_invariants_none();

        unsafe {
            (*self.ucell.get()).assume_init_ref()
        }
    }

    //////////////////////////////////
    // Untrusted functions below here

    #[inline(always)]
    pub fn into_inner(self, #[proof] perm: Permission<V>) -> V {
        requires([
            equal(self.id(), perm.pcell),
            perm.value.is_Some(),
        ]);
        ensures(|v|
            equal(v, perm.value.get_Some_0())
        );
        opens_invariants_none();

        #[proof] let mut perm = perm;
        self.take(&mut perm)
    }

    #[inline(always)]
    pub fn new(v: V) -> (PCell<V>, Proof<Permission<V>>) {
        ensures(|pt : (PCell<V>, Proof<Permission<V>>)|
            equal(pt.1, Proof(Permission{ pcell: pt.0.id(), value: option::Option::Some(v) }))
        );

        let (p, Proof(mut t)) = Self::empty();
        p.put(&mut t, v);
        (p, Proof(t))
    }
}
