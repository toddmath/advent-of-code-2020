pub use stable_deref_trait::{
    CloneStableDeref as CloneStableAddress, StableDeref as StableAddress,
};
use std::{
    borrow::Borrow,
    cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd},
    convert::From,
    fmt::{self, Debug},
    hash::{Hash, Hasher},
    marker::{Send, Sync},
    ops::{Deref, DerefMut},
};

pub struct OwningRef<O, T: ?Sized> {
    owner: O,
    reference: *const T,
}

#[allow(clippy::module_name_repetitions)]
pub struct OwningRefMut<O, T: ?Sized> {
    owner: O,
    reference: *mut T,
}

pub trait Erased {}
impl<T> Erased for T {}

/// Helper trait for erasing the concrete type of what an owner derferences to,
/// for example `Box<T> -> Box<dyn Erased>`.
pub unsafe trait IntoErased<'a> {
    /// Owner with the dereference type substituted to `Erased`.
    type Erased;
    /// Perform the type erasure.
    fn into_erased(self) -> Self::Erased;
}

impl<O, T: ?Sized> OwningRef<O, T> {
    /// Creates a new owning reference from a owner
    /// initialized to the direct dereference of it.
    pub fn new(o: O) -> Self
    where
        O: StableAddress + Deref<Target = T>,
    {
        Self {
            reference: &*o,
            owner: o,
        }
    }

    /// Like `new`, but doesn’t require `O` to implement the `StableAddress`
    /// trait. Instead, the caller is responsible to make the same promises
    /// as implementing the trait.
    ///
    /// This is useful for cases where coherence rules prevents implementing the
    /// trait
    ///
    /// # Safety
    pub unsafe fn new_assert_stable_address(o: O) -> Self
    where
        O: Deref<Target = T>,
    {
        Self {
            reference: &*o,
            owner: o,
        }
    }

    /// Converts `self` into a new owning reference that points at something
    /// reachable from the previous one.
    ///
    /// This can be a reference to a field of `U`, something reachable from a
    /// field of `U`, or even something unrelated with a `'static` lifetime.
    pub fn map<F, U: ?Sized>(self, f: F) -> OwningRef<O, U>
    where
        O: StableAddress,
        F: FnOnce(&T) -> &U,
    {
        OwningRef {
            reference: f(&self),
            owner: self.owner,
        }
    }

    /// Converts `self` into a new owning reference that points at something
    /// reachable from the previous one or from the owner itself.
    ///
    /// This can be a reference to a field of `U`, something reachable from a
    /// field of `U` or from the owner `O`, or even something unrelated with
    /// a `'static` lifetime.
    pub fn map_with_owner<F, U: ?Sized>(self, f: F) -> OwningRef<O, U>
    where
        O: StableAddress,
        F: for<'a> FnOnce(&'a O, &'a T) -> &'a U,
    {
        OwningRef {
            reference: f(&self.owner, &self),
            owner: self.owner,
        }
    }

    /// Tries to convert `self` into a new owning reference that points
    /// at something reachable from the previous one.
    ///
    /// This can be a reference to a field of `U`, something reachable from a
    /// field of `U`, or even something unrelated with a `'static` lifetime.
    pub fn try_map<F, U: ?Sized, E>(self, f: F) -> Result<OwningRef<O, U>, E>
    where
        O: StableAddress,
        F: FnOnce(&T) -> Result<&U, E>,
    {
        Ok(OwningRef {
            reference: f(&self)?,
            owner: self.owner,
        })
    }

    /// Tries to convert `self` into a new owning reference that points
    /// at something reachable from the previous one.
    ///
    /// This can be a reference to a field of `U`, something reachable from a
    /// field of `U`, or even something unrelated with a `'static` lifetime.
    pub fn try_map_with_owner<F, U: ?Sized, E>(
        self,
        f: F,
    ) -> Result<OwningRef<O, U>, E>
    where
        O: StableAddress,
        F: for<'a> FnOnce(&'a O, &'a T) -> Result<&'a U, E>,
    {
        Ok(OwningRef {
            reference: f(&self.owner, &self)?,
            owner: self.owner,
        })
    }

    /// Converts `self` into a new owning reference with a different owner type.
    ///
    /// The new owner type needs to still contain the original owner in some way
    /// so that the reference into it remains valid. This function is marked
    /// unsafe because the user needs to manually uphold this guarantee.
    pub unsafe fn map_owner<F, P>(self, f: F) -> OwningRef<P, T>
    where
        O: StableAddress,
        P: StableAddress,
        F: FnOnce(O) -> P,
    {
        OwningRef {
            reference: self.reference,
            owner: f(self.owner),
        }
    }

    /// Converts `self` into a new owning reference where the owner is wrapped
    /// in an additional `Box<O>`.
    ///
    /// This can be used to safely erase the owner of any `OwningRef<O, T>`
    /// to a `OwningRef<Box<dyn Erased>, T>`.
    pub fn map_owner_box(self) -> OwningRef<Box<O>, T> {
        OwningRef {
            reference: self.reference,
            owner: Box::new(self.owner),
        }
    }

    /// Erases the concrete base type of the owner with a trait object.
    ///
    /// This allows mixing of owned references with different owner base types.
    pub fn erase_owner<'a>(self) -> OwningRef<O::Erased, T>
    where
        O: IntoErased<'a>,
    {
        OwningRef {
            reference: self.reference,
            owner: self.owner.into_erased(),
        }
    }

    /// A reference to the underlying owner.
    pub fn as_owner(&self) -> &O {
        &self.owner
    }

    /// Discards the reference and retrieves the owner.
    pub fn into_owner(self) -> O {
        self.owner
    }
}

impl<O, T: ?Sized> OwningRefMut<O, T> {
    /// Creates a new owning reference from a owner
    /// initialized to the direct dereference of it.
    pub fn new(mut owner: O) -> Self
    where
        O: StableAddress + DerefMut<Target = T>,
    {
        Self {
            reference: &mut *owner,
            owner,
        }
    }

    /// Like `new`, but doesn’t require `O` to implement the `StableAddress`
    /// trait. Instead, the caller is responsible to make the same promises
    /// as implementing the trait.
    pub unsafe fn new_assert_stable_address(mut owner: O) -> Self
    where
        O: DerefMut<Target = T>,
    {
        OwningRefMut {
            reference: &mut *owner,
            owner,
        }
    }

    /// Converts `self` into a new _shared_ owning reference that points at
    /// something reachable from the previous one.
    ///
    /// This can be a reference to a field of `U`, something reachable from a
    /// field of `U`, or even something unrelated with a `'static` lifetime.
    pub fn map<F, U: ?Sized>(mut self, f: F) -> OwningRef<O, U>
    where
        O: StableAddress,
        F: FnOnce(&mut T) -> &U,
    {
        OwningRef {
            reference: f(&mut self),
            owner: self.owner,
        }
    }

    /// Converts `self` into a new _mutable_ owning reference that points at
    /// something reachable from the previous one.
    ///
    /// This can be a reference to a field of `U`, something reachable from a
    /// field of `U`, or even something unrelated with a `'static` lifetime.
    pub fn map_mut<F, U: ?Sized>(mut self, f: F) -> OwningRefMut<O, U>
    where
        O: StableAddress,
        F: FnOnce(&mut T) -> &mut U,
    {
        OwningRefMut {
            reference: f(&mut self),
            owner: self.owner,
        }
    }

    /// Tries to convert `self` into a new _shared_ owning reference that points
    /// at something reachable from the previous one.
    ///
    /// This can be a reference to a field of `U`, something reachable from a
    /// field of `U`, or even something unrelated with a `'static` lifetime.
    pub fn try_map<F, U: ?Sized, E>(
        mut self,
        f: F,
    ) -> Result<OwningRef<O, U>, E>
    where
        O: StableAddress,
        F: FnOnce(&mut T) -> Result<&U, E>,
    {
        Ok(OwningRef {
            reference: f(&mut self)?,
            owner: self.owner,
        })
    }

    /// Tries to convert `self` into a new _mutable_ owning reference that
    /// points at something reachable from the previous one.
    ///
    /// This can be a reference to a field of `U`, something reachable from a
    /// field of `U`, or even something unrelated with a `'static` lifetime.
    pub fn try_map_mut<F, U: ?Sized, E>(
        mut self,
        f: F,
    ) -> Result<OwningRefMut<O, U>, E>
    where
        O: StableAddress,
        F: FnOnce(&mut T) -> Result<&mut U, E>,
    {
        Ok(OwningRefMut {
            reference: f(&mut self)?,
            owner: self.owner,
        })
    }

    /// Converts `self` into a new owning reference with a different owner type.
    ///
    /// The new owner type needs to still contain the original owner in some way
    /// so that the reference into it remains valid. This function is marked
    /// unsafe because the user needs to manually uphold this guarantee.
    pub unsafe fn map_owner<F, P>(self, f: F) -> OwningRefMut<P, T>
    where
        O: StableAddress,
        P: StableAddress,
        F: FnOnce(O) -> P,
    {
        OwningRefMut {
            reference: self.reference,
            owner: f(self.owner),
        }
    }

    /// Converts `self` into a new owning reference where the owner is wrapped
    /// in an additional `Box<O>`.
    ///
    /// This can be used to safely erase the owner of any `OwningRefMut<O, T>`
    /// to a `OwningRefMut<Box<dyn Erased>, T>`.
    pub fn map_owner_box(self) -> OwningRefMut<Box<O>, T> {
        OwningRefMut {
            reference: self.reference,
            owner: Box::new(self.owner),
        }
    }

    /// Erases the concrete base type of the owner with a trait object.
    ///
    /// This allows mixing of owned references with different owner base types.
    pub fn erase_owner<'a>(self) -> OwningRefMut<O::Erased, T>
    where
        O: IntoErased<'a>,
    {
        OwningRefMut {
            reference: self.reference,
            owner: self.owner.into_erased(),
        }
    }

    /// A reference to the underlying owner.
    pub fn as_owner(&self) -> &O {
        &self.owner
    }

    /// A mutable reference to the underlying owner.
    pub fn as_owner_mut(&mut self) -> &mut O {
        &mut self.owner
    }

    /// Discards the reference and retrieves the owner.
    pub fn into_owner(self) -> O {
        self.owner
    }
}

/// `OwningHandle` is a complement to `OwningRef`. Where `OwningRef` allows
/// consumers to pass around an owned object and a dependent reference,
/// `OwningHandle` contains an owned object and a dependent _object_.
///
/// `OwningHandle` can encapsulate a `RefMut` along with its associated
/// `RefCell`, or an `RwLockReadGuard` along with its associated `RwLock`.
/// However, the API is completely generic and there are no restrictions on
/// what types of owning and dependent objects may be used.
///
/// `OwningHandle` is created by passing an owner object (which dereferences
/// to a stable address) along with a callback which receives a pointer to
/// that stable location. The callback may then dereference the pointer and
/// mint a dependent object, with the guarantee that the returned object will
/// not outlive the referent of the pointer.
///
/// Since the callback needs to dereference a raw pointer, it requires `unsafe`
/// code. To avoid forcing this unsafety on most callers, the `ToHandle` trait
/// is implemented for common data structures. Types that implement `ToHandle`
/// can be wrapped into an `OwningHandle` without passing a callback.
pub struct OwningHandle<O, H>
where
    O: StableAddress,
    H: Deref,
{
    handle: H,
    _owner: O,
}

impl<O, H> Deref for OwningHandle<O, H>
where
    O: StableAddress,
    H: Deref,
{
    type Target = H::Target;

    fn deref(&self) -> &Self::Target {
        &*self.handle
    }
}

unsafe impl<O, H> StableAddress for OwningHandle<O, H>
where
    O: StableAddress,
    H: StableAddress,
{
}

impl<O, H> DerefMut for OwningHandle<O, H>
where
    O: StableAddress,
    H: DerefMut,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.handle
    }
}

/// Trait to implement the conversion of owner to handle for common types.
pub trait ToHandle {
    /// The type of handle to be encapsulated by the `OwningHandle`.
    type Handle: Deref;

    /// Given an appropriately-long-lived pointer to ourselves, create a
    /// handle to be encapsulated by the `OwningHandle`.
    #[allow(clippy::wrong_self_convention)]
    unsafe fn to_handle(x: *const Self) -> Self::Handle;
}

/// Trait to implement the conversion of owner to mutable handle for common
/// types.
pub trait ToHandleMut {
    /// The type of handle to be encapsulated by the `OwningHandle`.
    type HandleMut: DerefMut;

    /// Given an appropriately-long-lived pointer to ourselves, create a
    /// mutable handle to be encapsulated by the `OwningHandle`.
    #[allow(clippy::wrong_self_convention)]
    unsafe fn to_handle_mut(x: *const Self) -> Self::HandleMut;
}

impl<O, H> OwningHandle<O, H>
where
    O: StableAddress,
    O::Target: ToHandle<Handle = H>,
    H: Deref,
{
    /// Create a new `OwningHandle` for a type that implements `ToHandle`. For
    /// types that don't implement `ToHandle`, callers may invoke
    /// `new_with_fn`, which accepts a callback to perform the conversion.
    pub fn new(owner: O) -> Self {
        OwningHandle::new_with_fn(owner, |x| unsafe { O::Target::to_handle(x) })
    }
}

impl<O, H> OwningHandle<O, H>
where
    O: StableAddress,
    O::Target: ToHandleMut<HandleMut = H>,
    H: DerefMut,
{
    /// Create a new mutable `OwningHandle` for a type that implements
    /// `ToHandleMut`.
    pub fn new_mut(owner: O) -> Self {
        OwningHandle::new_with_fn(owner, |x| unsafe {
            O::Target::to_handle_mut(x)
        })
    }
}

impl<O, H> OwningHandle<O, H>
where
    O: StableAddress,
    H: Deref,
{
    /// Create a new `OwningHandle`. The provided callback will be invoked with
    /// a pointer to the object owned by `o`, and the returned value is stored
    /// as the object to which this `OwningHandle` will forward `Deref` and
    /// `DerefMut`.
    pub fn new_with_fn<F>(owner: O, f: F) -> Self
    where
        F: FnOnce(*const O::Target) -> H,
    {
        let h: H;
        {
            h = f(&*owner as *const O::Target);
        }

        OwningHandle {
            handle: h,
            _owner: owner,
        }
    }

    /// Create a new `OwningHandle`. The provided callback will be invoked with
    /// a pointer to the object owned by `o`, and the returned value is stored
    /// as the object to which this `OwningHandle` will forward `Deref` and
    /// `DerefMut`.
    pub fn try_new<F, E>(owner: O, f: F) -> Result<Self, E>
    where
        F: FnOnce(*const O::Target) -> Result<H, E>,
    {
        let h: H;
        {
            h = f(&*owner as *const O::Target)?;
        }

        Ok(OwningHandle {
            handle: h,
            _owner: owner,
        })
    }

    #[allow(clippy::used_underscore_binding)]
    /// A getter for the underlying owner.
    pub fn as_owner(&self) -> &O {
        &self._owner
    }

    #[allow(clippy::used_underscore_binding)]
    /// Discards the dependent object and returns the owner.
    pub fn into_owner(self) -> O {
        self._owner
    }
}

impl<O, T: ?Sized> Deref for OwningRef<O, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.reference }
    }
}

impl<O, T: ?Sized> Deref for OwningRefMut<O, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.reference }
    }
}

impl<O, T: ?Sized> DerefMut for OwningRefMut<O, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.reference }
    }
}

unsafe impl<O, T: ?Sized> StableAddress for OwningRef<O, T> {}
unsafe impl<O, T: ?Sized> StableAddress for OwningRefMut<O, T> {}

impl<O, T: ?Sized> AsRef<T> for OwningRef<O, T> {
    fn as_ref(&self) -> &T {
        &*self
    }
}

impl<O, T: ?Sized> AsRef<T> for OwningRefMut<O, T> {
    fn as_ref(&self) -> &T {
        &*self
    }
}

impl<O, T: ?Sized> AsMut<T> for OwningRefMut<O, T> {
    fn as_mut(&mut self) -> &mut T {
        &mut *self
    }
}

impl<O, T: ?Sized> Borrow<T> for OwningRef<O, T> {
    fn borrow(&self) -> &T {
        &*self
    }
}

impl<O, T: ?Sized> From<O> for OwningRef<O, T>
where
    O: StableAddress + Deref<Target = T>,
{
    fn from(owner: O) -> Self {
        Self::new(owner)
    }
}

impl<O, T: ?Sized> From<O> for OwningRefMut<O, T>
where
    O: StableAddress + DerefMut<Target = T>,
{
    fn from(owner: O) -> Self {
        Self::new(owner)
    }
}

impl<O, T: ?Sized> From<OwningRefMut<O, T>> for OwningRef<O, T>
where
    O: StableAddress + DerefMut<Target = T>,
{
    fn from(other: OwningRefMut<O, T>) -> Self {
        OwningRef {
            owner: other.owner,
            reference: other.reference,
        }
    }
}

// TODO: Finish standard impls (Debug, etc.)
impl<O, T: ?Sized> Debug for OwningRef<O, T>
where
    O: Debug,
    T: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "OwningRef {{ owner: {:?}, reference: {:?} }}",
            self.as_owner(),
            &**self
        )
    }
}

impl<O, T: ?Sized> Debug for OwningRefMut<O, T>
where
    O: Debug,
    T: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "OwningRefMut {{ owner: {:?}, reference: {:?} }}",
            self.as_owner(),
            &**self
        )
    }
}

impl<O, T: ?Sized> Clone for OwningRef<O, T>
where
    O: CloneStableAddress,
{
    fn clone(&self) -> Self {
        Self {
            owner: self.owner.clone(),
            reference: self.reference,
        }
    }
}

unsafe impl<O, T: ?Sized> CloneStableAddress for OwningRef<O, T> where
    O: CloneStableAddress
{
}

unsafe impl<O, T: ?Sized> Send for OwningRef<O, T>
where
    O: Send,
    for<'a> &'a T: Send,
{
}
unsafe impl<O, T: ?Sized> Sync for OwningRef<O, T>
where
    O: Sync,
    for<'a> &'a T: Sync,
{
}

unsafe impl<O, T: ?Sized> Send for OwningRefMut<O, T>
where
    O: Send,
    for<'a> &'a mut T: Send,
{
}
unsafe impl<O, T: ?Sized> Sync for OwningRefMut<O, T>
where
    O: Sync,
    for<'a> &'a mut T: Sync,
{
}

impl Debug for dyn Erased {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<dyn Erased>")
    }
}

impl<O, T: ?Sized> PartialEq for OwningRef<O, T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        (&*self as &T).eq(&*other as &T)
    }
}

impl<O, T: ?Sized> Eq for OwningRef<O, T> where T: Eq {}

impl<O, T: ?Sized> PartialOrd for OwningRef<O, T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (&*self as &T).partial_cmp(&*other as &T)
    }
}

impl<O, T: ?Sized> Ord for OwningRef<O, T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        (&*self as &T).cmp(&*other as &T)
    }
}

impl<O, T: ?Sized> Hash for OwningRef<O, T>
where
    T: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&*self as &T).hash(state);
    }
}

impl<O, T: ?Sized> PartialEq for OwningRefMut<O, T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        (&*self as &T).eq(&*other as &T)
    }
}

impl<O, T: ?Sized> Eq for OwningRefMut<O, T> where T: Eq {}

impl<O, T: ?Sized> PartialOrd for OwningRefMut<O, T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (&*self as &T).partial_cmp(&*other as &T)
    }
}

impl<O, T: ?Sized> Ord for OwningRefMut<O, T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        (&*self as &T).cmp(&*other as &T)
    }
}

impl<O, T: ?Sized> Hash for OwningRefMut<O, T>
where
    T: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&*self as &T).hash(state);
    }
}

use std::{
    boxed::Box,
    cell::{Ref, RefCell, RefMut},
    rc::Rc,
    sync::{Arc, MutexGuard, RwLockReadGuard, RwLockWriteGuard},
};

impl<T: 'static> ToHandle for RefCell<T> {
    type Handle = Ref<'static, T>;

    unsafe fn to_handle(x: *const Self) -> Self::Handle {
        (*x).borrow()
    }
}

impl<T: 'static> ToHandleMut for RefCell<T> {
    type HandleMut = RefMut<'static, T>;

    unsafe fn to_handle_mut(x: *const Self) -> Self::HandleMut {
        (*x).borrow_mut()
    }
}

/// Typedef of a owning reference that uses a `Box` as the owner.
pub type BoxRef<T, U = T> = OwningRef<Box<T>, U>;
/// Typedef of a owning reference that uses a `Vec` as the owner.
pub type VecRef<T, U = T> = OwningRef<Vec<T>, U>;
/// Typedef of a owning reference that uses a `String` as the owner.
pub type StringRef = OwningRef<String, str>;

/// Typedef of a owning reference that uses a `Rc` as the owner.
pub type RcRef<T, U = T> = OwningRef<Rc<T>, U>;
/// Typedef of a owning reference that uses a `Arc` as the owner.
pub type ArcRef<T, U = T> = OwningRef<Arc<T>, U>;

/// Typedef of a owning reference that uses a `Ref` as the owner.
pub type RefRef<'a, T, U = T> = OwningRef<Ref<'a, T>, U>;
/// Typedef of a owning reference that uses a `RefMut` as the owner.
pub type RefMutRef<'a, T, U = T> = OwningRef<RefMut<'a, T>, U>;
/// Typedef of a owning reference that uses a `MutexGuard` as the owner.
pub type MutexGuardRef<'a, T, U = T> = OwningRef<MutexGuard<'a, T>, U>;
/// Typedef of a owning reference that uses a `RwLockReadGuard` as the owner.
pub type RwLockReadGuardRef<'a, T, U = T> =
    OwningRef<RwLockReadGuard<'a, T>, U>;
/// Typedef of a owning reference that uses a `RwLockWriteGuard` as the owner.
pub type RwLockWriteGuardRef<'a, T, U = T> =
    OwningRef<RwLockWriteGuard<'a, T>, U>;

/// Typedef of a mutable owning reference that uses a `Box` as the owner.
pub type BoxRefMut<T, U = T> = OwningRefMut<Box<T>, U>;
/// Typedef of a mutable owning reference that uses a `Vec` as the owner.
pub type VecRefMut<T, U = T> = OwningRefMut<Vec<T>, U>;
/// Typedef of a mutable owning reference that uses a `String` as the owner.
pub type StringRefMut = OwningRefMut<String, str>;

/// Typedef of a mutable owning reference that uses a `RefMut` as the owner.
pub type RefMutRefMut<'a, T, U = T> = OwningRefMut<RefMut<'a, T>, U>;
/// Typedef of a mutable owning reference that uses a `MutexGuard` as the owner.
pub type MutexGuardRefMut<'a, T, U = T> = OwningRefMut<MutexGuard<'a, T>, U>;
/// Typedef of a mutable owning reference that uses a `RwLockWriteGuard` as the
/// owner.
pub type RwLockWriteGuardRefMut<'a, T, U = T> =
    OwningRefMut<RwLockWriteGuard<'a, T>, U>;

unsafe impl<'a, T: 'a> IntoErased<'a> for Box<T> {
    type Erased = Box<dyn Erased + 'a>;

    fn into_erased(self) -> Self::Erased {
        self
    }
}

unsafe impl<'a, T: 'a> IntoErased<'a> for Rc<T> {
    type Erased = Rc<dyn Erased + 'a>;

    fn into_erased(self) -> Self::Erased {
        self
    }
}

unsafe impl<'a, T: 'a> IntoErased<'a> for Arc<T> {
    type Erased = Arc<dyn Erased + 'a>;

    fn into_erased(self) -> Self::Erased {
        self
    }
}

/// Typedef of a owning reference that uses an erased `Box` as the owner.
pub type ErasedBoxRef<U> = OwningRef<Box<dyn Erased>, U>;
/// Typedef of a owning reference that uses an erased `Rc` as the owner.
pub type ErasedRcRef<U> = OwningRef<Rc<dyn Erased>, U>;
/// Typedef of a owning reference that uses an erased `Arc` as the owner.
pub type ErasedArcRef<U> = OwningRef<Arc<dyn Erased>, U>;

/// Typedef of a mutable owning reference that uses an erased `Box` as the
/// owner.
pub type ErasedBoxRefMut<U> = OwningRefMut<Box<dyn Erased>, U>;

#[cfg(test)]
mod tests {
    mod owning_ref {
        use super::super::{BoxRef, Erased, ErasedBoxRef, OwningRef, RcRef};
        use std::{
            cmp::{Ord, Ordering, PartialEq, PartialOrd},
            collections::{hash_map::DefaultHasher, HashMap},
            hash::{Hash, Hasher},
            rc::Rc,
        };

        #[derive(Debug, PartialEq)]
        struct Example(u32, String, [u8; 3]);

        fn example() -> Example {
            Example(42, "hello world".to_string(), [1, 2, 3])
        }

        #[test]
        fn new_deref() {
            let or: OwningRef<Box<()>, ()> = OwningRef::new(Box::new(()));
            assert_eq!(&*or, &());
        }

        #[test]
        fn into() {
            let or: OwningRef<Box<()>, ()> = Box::new(()).into();
            assert_eq!(&*or, &());
        }

        #[test]
        fn map_offset_ref() {
            let or: BoxRef<Example> = Box::new(example()).into();
            let or: BoxRef<_, u32> = or.map(|x| &x.0);
            assert_eq!(&*or, &42);

            let or: BoxRef<Example> = Box::new(example()).into();
            let or: BoxRef<_, u8> = or.map(|x| &x.2[1]);
            assert_eq!(&*or, &2);
        }

        #[test]
        fn map_heap_ref() {
            let or: BoxRef<Example> = Box::new(example()).into();
            let or: BoxRef<_, str> = or.map(|x| &x.1[..5]);
            assert_eq!(&*or, "hello");
        }

        #[test]
        fn map_static_ref() {
            let or: BoxRef<()> = Box::new(()).into();
            let or: BoxRef<_, str> = or.map(|_| "hello");
            assert_eq!(&*or, "hello");
        }

        #[test]
        fn map_chained() {
            let or: BoxRef<String> = Box::new(example().1).into();
            let or: BoxRef<_, str> = or.map(|x| &x[1..5]);
            let or: BoxRef<_, str> = or.map(|x| &x[..2]);
            assert_eq!(&*or, "el");
        }

        #[test]
        fn map_chained_inference() {
            let or = BoxRef::new(Box::new(example().1))
                .map(|x| &x[..5])
                .map(|x| &x[1..3]);
            assert_eq!(&*or, "el");
        }

        #[test]
        fn as_owner() {
            let or: BoxRef<String> = Box::new(example().1).into();
            let or = or.map(|x| &x[..5]);
            assert_eq!(&*or, "hello");
            assert_eq!(&**or.as_owner(), "hello world");
        }

        #[test]
        fn into_owner() {
            let or: BoxRef<String> = Box::new(example().1).into();
            let or = or.map(|x| &x[..5]);
            assert_eq!(&*or, "hello");
            let s = *or.into_owner();
            assert_eq!(&s, "hello world");
        }

        #[test]
        fn fmt_debug() {
            let or: BoxRef<String> = Box::new(example().1).into();
            let or = or.map(|x| &x[..5]);
            let s = format!("{:?}", or);
            assert_eq!(
                &s,
                "OwningRef { owner: \"hello world\", reference: \"hello\" }"
            );
        }

        #[test]
        fn erased_owner() {
            let o1: BoxRef<Example, str> =
                BoxRef::new(Box::new(example())).map(|x| &x.1[..]);

            let o2: BoxRef<String, str> =
                BoxRef::new(Box::new(example().1)).map(|x| &x[..]);

            let os: Vec<ErasedBoxRef<str>> =
                vec![o1.erase_owner(), o2.erase_owner()];
            assert!(os.iter().all(|e| &e[..] == "hello world"));
        }

        #[allow(clippy::blacklisted_name, clippy::items_after_statements)]
        #[test]
        fn non_static_erased_owner() {
            let foo = [413, 612];
            let bar = &foo;

            // FIXME: lifetime inference fails us, and we can't easily define a
            // lifetime for a closure (see https://github.com/rust-lang/rust/issues/22340)
            // So we use a function to identify the lifetimes instead.
            fn borrow<'a>(a: &'a &[i32; 2]) -> &'a i32 {
                &a[0]
            }

            let o: BoxRef<&[i32; 2]> = Box::new(bar).into();
            let o: BoxRef<&[i32; 2], i32> = o.map(borrow);
            let o: BoxRef<dyn Erased, i32> = o.erase_owner();

            assert_eq!(*o, 413);
        }

        // #[test]
        // fn raii_locks() {
        //     use super::super::{
        //         MutexGuardRef, RefMutRef, RefRef, RwLockReadGuardRef,
        //         RwLockWriteGuardRef,
        //     };
        //     use std::{
        //         cell::RefCell,
        //         sync::{Mutex, RwLock},
        //     };

        //     {
        //         let a = RefCell::new(1);
        //         let a = {
        //             let a = RefRef::new(a.borrow());
        //             assert_eq!(*a, 1);
        //             a
        //         };
        //         assert_eq!(*a, 1);
        //         drop(a);
        //     }
        //     {
        //         let a = RefCell::new(1);
        //         let a = {
        //             let a = RefMutRef::new(a.borrow_mut());
        //             assert_eq!(*a, 1);
        //             a
        //         };
        //         assert_eq!(*a, 1);
        //         drop(a);
        //     }
        //     {
        //         let a = Mutex::new(1);
        //         let a = {
        //             let a = MutexGuardRef::new(a.lock().unwrap());
        //             assert_eq!(*a, 1);
        //             a
        //         };
        //         assert_eq!(*a, 1);
        //         drop(a);
        //     }
        //     {
        //         let a = RwLock::new(1);
        //         let a = {
        //             let a = RwLockReadGuardRef::new(a.read().unwrap());
        //             assert_eq!(*a, 1);
        //             a
        //         };
        //         assert_eq!(*a, 1);
        //         drop(a);
        //     }
        //     {
        //         let a = RwLock::new(1);
        //         let a = {
        //             let a = RwLockWriteGuardRef::new(a.write().unwrap());
        //             assert_eq!(*a, 1);
        //             a
        //         };
        //         assert_eq!(*a, 1);
        //         drop(a);
        //     }
        // }

        #[test]
        fn eq() {
            let or1: BoxRef<[u8]> =
                BoxRef::new(vec![1, 2, 3].into_boxed_slice());
            let or2: BoxRef<[u8]> =
                BoxRef::new(vec![1, 2, 3].into_boxed_slice());
            assert_eq!(or1.eq(&or2), true);
        }

        #[test]
        fn cmp() {
            let or1: BoxRef<[u8]> =
                BoxRef::new(vec![1, 2, 3].into_boxed_slice());
            let or2: BoxRef<[u8]> =
                BoxRef::new(vec![4, 5, 6].into_boxed_slice());
            assert_eq!(or1.cmp(&or2), Ordering::Less);
        }

        #[test]
        fn partial_cmp() {
            let or1: BoxRef<[u8]> =
                BoxRef::new(vec![4, 5, 6].into_boxed_slice());
            let or2: BoxRef<[u8]> =
                BoxRef::new(vec![1, 2, 3].into_boxed_slice());
            assert_eq!(or1.partial_cmp(&or2), Some(Ordering::Greater));
        }

        #[test]
        fn hash() {
            let mut h1 = DefaultHasher::new();
            let mut h2 = DefaultHasher::new();

            let or1: BoxRef<[u8]> =
                BoxRef::new(vec![1, 2, 3].into_boxed_slice());
            let or2: BoxRef<[u8]> =
                BoxRef::new(vec![1, 2, 3].into_boxed_slice());

            or1.hash(&mut h1);
            or2.hash(&mut h2);

            assert_eq!(h1.finish(), h2.finish());
        }

        #[test]
        fn borrow() {
            let mut hash = HashMap::new();
            let key = RcRef::<String>::new(Rc::new("foo-bar".to_string()))
                .map(|s| &s[..]);

            hash.insert(key.clone().map(|s| &s[..3]), 42);
            hash.insert(key.map(|s| &s[4..]), 23);

            assert_eq!(hash.get("foo"), Some(&42));
            assert_eq!(hash.get("bar"), Some(&23));
        }

        #[allow(clippy::many_single_char_names)]
        #[test]
        fn total_erase() {
            let a: OwningRef<Vec<u8>, [u8]> =
                OwningRef::new(vec![]).map(|x| &x[..]);
            let b: OwningRef<Box<[u8]>, [u8]> =
                OwningRef::new(vec![].into_boxed_slice()).map(|x| &x[..]);

            let c: OwningRef<Rc<Vec<u8>>, [u8]> =
                unsafe { a.map_owner(Rc::new) };
            let d: OwningRef<Rc<Box<[u8]>>, [u8]> =
                unsafe { b.map_owner(Rc::new) };

            let e: OwningRef<Rc<dyn Erased>, [u8]> = c.erase_owner();
            let f: OwningRef<Rc<dyn Erased>, [u8]> = d.erase_owner();

            let _g = e.clone();
            let _h = f.clone();
        }

        #[test]
        fn total_erase_box() {
            let a: OwningRef<Vec<u8>, [u8]> =
                OwningRef::new(vec![]).map(|x| &x[..]);
            let b: OwningRef<Box<[u8]>, [u8]> =
                OwningRef::new(vec![].into_boxed_slice()).map(|x| &x[..]);

            let c: OwningRef<Box<Vec<u8>>, [u8]> = a.map_owner_box();
            let d: OwningRef<Box<Box<[u8]>>, [u8]> = b.map_owner_box();

            let _e: OwningRef<Box<dyn Erased>, [u8]> = c.erase_owner();
            let _f: OwningRef<Box<dyn Erased>, [u8]> = d.erase_owner();
        }

        #[test]
        fn try_map1() {
            use std::any::Any;

            let x = Box::new(123_i32);
            let y: Box<dyn Any> = x;

            OwningRef::new(y)
                .try_map(|x| x.downcast_ref::<i32>().ok_or(()))
                .unwrap();
        }

        #[test]
        fn try_map2() {
            use std::any::Any;

            let x = Box::new(123_u32);
            let y: Box<dyn Any> = x;

            OwningRef::new(y)
                .try_map(|x| x.downcast_ref::<i32>().ok_or(()))
                .unwrap_err();
        }

        #[test]
        fn map_with_owner() {
            let owning_ref: BoxRef<Example> = Box::new(example()).into();
            let owning_ref = owning_ref.map(|owner| &owner.1);

            owning_ref.map_with_owner(|owner, ref_field| {
                assert_eq!(owner.1, *ref_field);
                ref_field
            });
        }

        #[test]
        fn try_map_with_owner_ok() {
            let owning_ref: BoxRef<Example> = Box::new(example()).into();
            let owning_ref = owning_ref.map(|owner| &owner.1);

            owning_ref
                .try_map_with_owner(|owner, ref_field| {
                    assert_eq!(owner.1, *ref_field);
                    Ok(ref_field) as Result<_, ()>
                })
                .unwrap();
        }

        #[test]
        fn try_map_with_owner_err() {
            let owning_ref: BoxRef<Example> = Box::new(example()).into();
            let owning_ref = owning_ref.map(|owner| &owner.1);

            owning_ref
                .try_map_with_owner(|owner, ref_field| {
                    assert_eq!(owner.1, *ref_field);
                    Err(()) as Result<&(), _>
                })
                .unwrap_err();
        }
    }

    mod owning_handle {
        use super::super::{OwningHandle, RcRef};
        use std::{
            cell::RefCell,
            rc::Rc,
            sync::{Arc, RwLock},
        };

        #[test]
        fn owning_handle() {
            let cell = Rc::new(RefCell::new(2));
            let cell_ref = RcRef::new(cell);
            let mut handle = OwningHandle::new_with_fn(cell_ref, |x| {
                unsafe { x.as_ref() }.unwrap().borrow_mut()
            });
            assert_eq!(*handle, 2);
            *handle = 3;
            assert_eq!(*handle, 3);
        }

        #[test]
        fn try_owning_handle_ok() {
            let cell = Rc::new(RefCell::new(2));
            let cell_ref = RcRef::new(cell);
            let mut handle = OwningHandle::try_new::<_, ()>(cell_ref, |x| {
                Ok(unsafe { x.as_ref() }.unwrap().borrow_mut())
            })
            .unwrap();
            assert_eq!(*handle, 2);
            *handle = 3;
            assert_eq!(*handle, 3);
        }

        #[test]
        fn try_owning_handle_err() {
            let cell = Rc::new(RefCell::new(2));
            let cell_ref = RcRef::new(cell);
            let handle = OwningHandle::try_new::<_, ()>(cell_ref, |x| {
                if false {
                    return Ok(unsafe { x.as_ref() }.unwrap().borrow_mut());
                }
                Err(())
            });
            assert!(handle.is_err());
        }

        #[test]
        fn nested() {
            let result = {
                let complex =
                    Rc::new(RefCell::new(Arc::new(RwLock::new("someString"))));
                let curr = RcRef::new(complex);
                let curr = OwningHandle::new_with_fn(curr, |x| {
                    unsafe { x.as_ref() }.unwrap().borrow_mut()
                });
                let mut curr = OwningHandle::new_with_fn(curr, |x| {
                    unsafe { x.as_ref() }.unwrap().try_write().unwrap()
                });
                assert_eq!(*curr, "someString");
                *curr = "someOtherString";
                curr
            };
            assert_eq!(*result, "someOtherString");
        }

        #[test]
        fn owning_handle_safe() {
            let cell = Rc::new(RefCell::new(2));
            let cell_ref = RcRef::new(cell);
            let handle = OwningHandle::new(cell_ref);
            assert_eq!(*handle, 2);
        }

        #[test]
        fn owning_handle_mut_safe() {
            let cell = Rc::new(RefCell::new(2));
            let cell_ref = RcRef::new(cell);
            let mut handle = OwningHandle::new_mut(cell_ref);
            assert_eq!(*handle, 2);
            *handle = 3;
            assert_eq!(*handle, 3);
        }

        #[test]
        fn owning_handle_safe_2() {
            let result = {
                let complex =
                    Rc::new(RefCell::new(Arc::new(RwLock::new("someString"))));
                let curr = RcRef::new(complex);
                let curr = OwningHandle::new_with_fn(curr, |x| {
                    unsafe { x.as_ref() }.unwrap().borrow_mut()
                });
                let mut curr = OwningHandle::new_with_fn(curr, |x| {
                    unsafe { x.as_ref() }.unwrap().try_write().unwrap()
                });
                assert_eq!(*curr, "someString");
                *curr = "someOtherString";
                curr
            };
            assert_eq!(*result, "someOtherString");
        }
    }

    mod owning_ref_mut {
        use super::super::{
            BoxRef, BoxRefMut, Erased, ErasedBoxRefMut, OwningRefMut,
        };
        use std::{
            cmp::{Ord, Ordering, PartialEq, PartialOrd},
            collections::{hash_map::DefaultHasher, HashMap},
            hash::{Hash, Hasher},
        };

        #[derive(Debug, PartialEq)]
        struct Example(u32, String, [u8; 3]);

        fn example() -> Example {
            Example(42, "hello world".to_string(), [1, 2, 3])
        }

        #[test]
        fn new_deref() {
            let or: OwningRefMut<Box<()>, ()> =
                OwningRefMut::new(Box::default());
            assert_eq!(&*or, &());
        }

        #[test]
        fn new_deref_mut() {
            let mut or: OwningRefMut<Box<()>, ()> =
                OwningRefMut::new(Box::new(()));
            assert_eq!(&mut *or, &mut ());
        }

        #[test]
        fn mutate() {
            let mut or: OwningRefMut<Box<usize>, usize> =
                OwningRefMut::new(Box::new(0));
            assert_eq!(&*or, &0);
            *or = 1;
            assert_eq!(&*or, &1);
        }

        #[test]
        fn into() {
            let or: OwningRefMut<Box<()>, ()> = Box::new(()).into();
            assert_eq!(&*or, &());
        }

        #[test]
        fn map_offset_ref() {
            let or: BoxRefMut<Example> = Box::new(example()).into();
            let or: BoxRef<_, u32> = or.map(|x| &mut x.0);
            assert_eq!(&*or, &42);

            let or: BoxRefMut<Example> = Box::new(example()).into();
            let or: BoxRef<_, u8> = or.map(|x| &mut x.2[1]);
            assert_eq!(&*or, &2);
        }

        #[test]
        fn map_heap_ref() {
            let or: BoxRefMut<Example> = Box::new(example()).into();
            let or: BoxRef<_, str> = or.map(|x| &mut x.1[..5]);
            assert_eq!(&*or, "hello");
        }

        #[test]
        fn map_static_ref() {
            let or: BoxRefMut<()> = Box::new(()).into();
            let or: BoxRef<_, str> = or.map(|_| "hello");
            assert_eq!(&*or, "hello");
        }

        #[test]
        fn map_mut_offset_ref() {
            let or: BoxRefMut<Example> = Box::new(example()).into();
            let or: BoxRefMut<_, u32> = or.map_mut(|x| &mut x.0);
            assert_eq!(&*or, &42);

            let or: BoxRefMut<Example> = Box::new(example()).into();
            let or: BoxRefMut<_, u8> = or.map_mut(|x| &mut x.2[1]);
            assert_eq!(&*or, &2);
        }

        #[test]
        fn map_mut_heap_ref() {
            let or: BoxRefMut<Example> = Box::new(example()).into();
            let or: BoxRefMut<_, str> = or.map_mut(|x| &mut x.1[..5]);
            assert_eq!(&*or, "hello");
        }

        #[test]
        fn map_mut_static_ref() {
            static mut MUT_S: [u8; 5] = *b"hello";

            let mut_s: &'static mut [u8] = unsafe { &mut MUT_S };

            let or: BoxRefMut<()> = Box::new(()).into();
            let or: BoxRefMut<_, [u8]> = or.map_mut(move |_| mut_s);
            assert_eq!(&*or, b"hello");
        }

        #[test]
        fn map_mut_chained() {
            let or: BoxRefMut<String> = Box::new(example().1).into();
            let or: BoxRefMut<_, str> = or.map_mut(|x| &mut x[1..5]);
            let or: BoxRefMut<_, str> = or.map_mut(|x| &mut x[..2]);
            assert_eq!(&*or, "el");
        }

        #[test]
        fn map_chained_inference() {
            let or = BoxRefMut::new(Box::new(example().1))
                .map_mut(|x| &mut x[..5])
                .map_mut(|x| &mut x[1..3]);
            assert_eq!(&*or, "el");
        }

        #[test]
        fn try_map_mut() {
            let or: BoxRefMut<String> = Box::new(example().1).into();
            let or: Result<BoxRefMut<_, str>, ()> =
                or.try_map_mut(|x| Ok(&mut x[1..5]));
            assert_eq!(&*or.unwrap(), "ello");

            let or: BoxRefMut<String> = Box::new(example().1).into();
            let or: Result<BoxRefMut<_, str>, ()> = or.try_map_mut(|_| Err(()));
            assert!(or.is_err());
        }

        #[test]
        fn as_owner() {
            let or: BoxRefMut<String> = Box::new(example().1).into();
            let or = or.map_mut(|x| &mut x[..5]);
            assert_eq!(&*or, "hello");
            assert_eq!(&**or.as_owner(), "hello world");
        }

        #[test]
        fn into_owner() {
            let or: BoxRefMut<String> = Box::new(example().1).into();
            let or = or.map_mut(|x| &mut x[..5]);
            assert_eq!(&*or, "hello");
            let s = *or.into_owner();
            assert_eq!(&s, "hello world");
        }

        #[test]
        fn fmt_debug() {
            let or: BoxRefMut<String> = Box::new(example().1).into();
            let or = or.map_mut(|x| &mut x[..5]);
            let s = format!("{:?}", or);
            assert_eq!(
                &s,
                "OwningRefMut { owner: \"hello world\", reference: \"hello\" }"
            );
        }

        #[test]
        fn erased_owner() {
            let o1: BoxRefMut<Example, str> =
                BoxRefMut::new(Box::new(example())).map_mut(|x| &mut x.1[..]);

            let o2: BoxRefMut<String, str> =
                BoxRefMut::new(Box::new(example().1)).map_mut(|x| &mut x[..]);

            let os: Vec<ErasedBoxRefMut<str>> =
                vec![o1.erase_owner(), o2.erase_owner()];
            assert!(os.iter().all(|e| &e[..] == "hello world"));
        }

        #[allow(
            clippy::blacklisted_name,
            clippy::items_after_statements,
            clippy::mut_mut
        )]
        #[test]
        fn non_static_erased_owner() {
            let mut foo = [413, 612];
            let bar = &mut foo;

            // FIXME: lifetime inference fails us, and we can't easily define a
            // lifetime for a closure (see https://github.com/rust-lang/rust/issues/22340)
            // So we use a function to identify the lifetimes instead.
            fn borrow<'a>(a: &'a mut &mut [i32; 2]) -> &'a mut i32 {
                &mut a[0]
            }

            let o: BoxRefMut<&mut [i32; 2]> = Box::new(bar).into();
            let o: BoxRefMut<&mut [i32; 2], i32> = o.map_mut(borrow);
            let o: BoxRefMut<dyn Erased, i32> = o.erase_owner();

            assert_eq!(*o, 413);
        }

        // #[test]
        // fn raii_locks() {
        //     use super::super::{
        //         MutexGuardRefMut, RefMutRefMut, RwLockWriteGuardRefMut,
        //     };
        //     use std::{
        //         cell::RefCell,
        //         sync::{Mutex, RwLock},
        //     };

        //     {
        //         let a = RefCell::new(1);
        //         let a = {
        //             let a = RefMutRefMut::new(a.borrow_mut());
        //             assert_eq!(*a, 1);
        //             a
        //         };
        //         assert_eq!(*a, 1);
        //         drop(a);
        //     }
        //     {
        //         let a = Mutex::new(1);
        //         let a = {
        //             let a = MutexGuardRefMut::new(a.lock().unwrap());
        //             assert_eq!(*a, 1);
        //             a
        //         };
        //         assert_eq!(*a, 1);
        //         drop(a);
        //     }
        //     {
        //         let a = RwLock::new(1);
        //         let a = {
        //             let a = RwLockWriteGuardRefMut::new(a.write().unwrap());
        //             assert_eq!(*a, 1);
        //             a
        //         };
        //         assert_eq!(*a, 1);
        //         drop(a);
        //     }
        // }

        #[test]
        fn eq() {
            let or1: BoxRefMut<[u8]> =
                BoxRefMut::new(vec![1, 2, 3].into_boxed_slice());
            let or2: BoxRefMut<[u8]> =
                BoxRefMut::new(vec![1, 2, 3].into_boxed_slice());
            assert_eq!(or1.eq(&or2), true);
        }

        #[test]
        fn cmp() {
            let or1: BoxRefMut<[u8]> =
                BoxRefMut::new(vec![1, 2, 3].into_boxed_slice());
            let or2: BoxRefMut<[u8]> =
                BoxRefMut::new(vec![4, 5, 6].into_boxed_slice());
            assert_eq!(or1.cmp(&or2), Ordering::Less);
        }

        #[test]
        fn partial_cmp() {
            let or1: BoxRefMut<[u8]> =
                BoxRefMut::new(vec![4, 5, 6].into_boxed_slice());
            let or2: BoxRefMut<[u8]> =
                BoxRefMut::new(vec![1, 2, 3].into_boxed_slice());
            assert_eq!(or1.partial_cmp(&or2), Some(Ordering::Greater));
        }

        #[test]
        fn hash() {
            let mut h1 = DefaultHasher::new();
            let mut h2 = DefaultHasher::new();

            let or1: BoxRefMut<[u8]> =
                BoxRefMut::new(vec![1, 2, 3].into_boxed_slice());
            let or2: BoxRefMut<[u8]> =
                BoxRefMut::new(vec![1, 2, 3].into_boxed_slice());

            or1.hash(&mut h1);
            or2.hash(&mut h2);

            assert_eq!(h1.finish(), h2.finish());
        }

        #[test]
        fn borrow() {
            let mut hash = HashMap::new();
            let key1 = BoxRefMut::<String>::new(Box::new("foo".to_string()))
                .map(|s| &s[..]);
            let key2 = BoxRefMut::<String>::new(Box::new("bar".to_string()))
                .map(|s| &s[..]);

            hash.insert(key1, 42);
            hash.insert(key2, 23);

            assert_eq!(hash.get("foo"), Some(&42));
            assert_eq!(hash.get("bar"), Some(&23));
        }

        #[test]
        fn total_erase() {
            let a: OwningRefMut<Vec<u8>, [u8]> =
                OwningRefMut::new(vec![]).map_mut(|x| &mut x[..]);
            let b: OwningRefMut<Box<[u8]>, [u8]> =
                OwningRefMut::new(vec![].into_boxed_slice())
                    .map_mut(|x| &mut x[..]);

            let c: OwningRefMut<Box<Vec<u8>>, [u8]> =
                unsafe { a.map_owner(Box::new) };
            let d: OwningRefMut<Box<Box<[u8]>>, [u8]> =
                unsafe { b.map_owner(Box::new) };

            let _e: OwningRefMut<Box<dyn Erased>, [u8]> = c.erase_owner();
            let _f: OwningRefMut<Box<dyn Erased>, [u8]> = d.erase_owner();
        }

        #[test]
        fn total_erase_box() {
            let a: OwningRefMut<Vec<u8>, [u8]> =
                OwningRefMut::new(vec![]).map_mut(|x| &mut x[..]);
            let b: OwningRefMut<Box<[u8]>, [u8]> =
                OwningRefMut::new(vec![].into_boxed_slice())
                    .map_mut(|x| &mut x[..]);

            let c: OwningRefMut<Box<Vec<u8>>, [u8]> = a.map_owner_box();
            let d: OwningRefMut<Box<Box<[u8]>>, [u8]> = b.map_owner_box();

            let _e: OwningRefMut<Box<dyn Erased>, [u8]> = c.erase_owner();
            let _f: OwningRefMut<Box<dyn Erased>, [u8]> = d.erase_owner();
        }

        #[test]
        fn try_map1() {
            use std::any::Any;

            let x = Box::new(123_i32);
            let y: Box<dyn Any> = x;

            OwningRefMut::new(y)
                .try_map_mut(|x| x.downcast_mut::<i32>().ok_or(()))
                .unwrap();
        }

        #[test]
        fn try_map2() {
            use std::any::Any;

            let x = Box::new(123_u32);
            let y: Box<dyn Any> = x;

            OwningRefMut::new(y)
                .try_map_mut(|x| x.downcast_mut::<i32>().ok_or(()))
                .unwrap_err();
        }

        #[test]
        fn try_map3() {
            use std::any::Any;

            let x = Box::new(123_i32);
            let y: Box<dyn Any> = x;

            OwningRefMut::new(y)
                .try_map(|x| x.downcast_ref::<i32>().ok_or(()))
                .unwrap();
        }

        #[test]
        fn try_map4() {
            use std::any::Any;

            let x = Box::new(123_u32);
            let y: Box<dyn Any> = x;

            OwningRefMut::new(y)
                .try_map(|x| x.downcast_ref::<i32>().ok_or(()))
                .unwrap_err();
        }

        #[test]
        fn into_owning_ref() {
            use super::super::BoxRef;

            let or: BoxRefMut<()> = Box::new(()).into();
            let or: BoxRef<()> = or.into();
            assert_eq!(&*or, &());
        }

        struct Foo {
            u: u32,
        }
        struct Bar {
            f: Foo,
        }

        #[test]
        fn ref_mut() {
            use std::cell::RefCell;

            let a = RefCell::new(Bar { f: Foo { u: 42 } });
            let mut b = OwningRefMut::new(a.borrow_mut());
            assert_eq!(b.f.u, 42);
            b.f.u = 43;
            let mut c = b.map_mut(|x| &mut x.f);
            assert_eq!(c.u, 43);
            c.u = 44;
            let mut d = c.map_mut(|x| &mut x.u);
            assert_eq!(*d, 44);
            *d = 45;
            assert_eq!(*d, 45);
        }
    }
}
