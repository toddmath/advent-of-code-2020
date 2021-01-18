use crate::arena::Bump;
use std::{
    any::Any,
    borrow,
    cmp::Ordering,
    convert::TryFrom,
    fmt,
    future::Future,
    hash::{Hash, Hasher},
    iter::FusedIterator,
    mem,
    ops::{Deref, DerefMut},
    pin::Pin,
    task::{Context, Poll},
};

/// An owned pointer to a bump-allocated `T` value, that runs `Drop`
/// implementations.
#[repr(transparent)]
pub struct Box<'a, T: ?Sized>(&'a mut T);

impl<'a, T> Box<'a, T> {
    /// Allocates memory on the heap and then places `x` into it.
    ///
    /// This doesn't actually allocate if `T` is zero-sized.
    #[inline(always)]
    pub fn new_in(x: T, a: &'a Bump) -> Self {
        Self(a.alloc(x))
    }

    /// Constructs a new `Pin<Box<T>>`. If `T` does not implement `Unpin`, then
    /// `x` will be pinned in memory and unable to be moved.
    #[inline(always)]
    pub fn pin_in(x: T, a: &'a Bump) -> Pin<Box<'a, T>> {
        Self(a.alloc(x)).into()
    }
}

impl<'a, T: ?Sized> Box<'a, T> {
    /// Constructs a box from a raw pointer.
    ///
    /// After calling this function, the raw pointer is owned by the
    /// resulting `Box`. Specifically, the `Box` destructor will call
    /// the destructor of `T` and free the allocated memory. For this
    /// to be safe, the memory must have been allocated in accordance
    /// with the [memory layout] used by `Box` .
    ///
    /// # Safety
    ///
    /// This function is unsafe because improper use may lead to
    /// memory problems. For example, a double-free may occur if the
    /// function is called twice on the same raw pointer.
    #[inline]
    pub unsafe fn from_raw(raw: *mut T) -> Self {
        Self(&mut *raw)
    }

    /// Consumes the `Box`, returning a wrapped raw pointer.
    ///
    /// The pointer will be properly aligned and non-null.
    ///
    /// After calling this function, the caller is responsible for the
    /// value previously managed by the `Box`. In particular, the
    /// caller should properly destroy `T`. The easiest way to
    /// do this is to convert the raw pointer back into a `Box` with the
    /// [`Box::from_raw`] function, allowing the `Box` destructor to perform
    /// the cleanup.
    ///
    /// Note: this is an associated function, which means that you have
    /// to call it as `Box::into_raw(b)` instead of `b.into_raw()`. This
    /// is so that there is no conflict with a method on the inner type.
    #[inline]
    pub fn into_raw(b: Box<'a, T>) -> *mut T {
        let ptr = b.0 as *mut T;
        mem::forget(b);
        ptr
    }

    /// Consumes and leaks the `Box`, returning a mutable reference,
    /// `&'a mut T`. Note that the type `T` must outlive the chosen lifetime
    /// `'a`. If the type has only static references, or none at all, then this
    /// may be chosen to be `'static`.
    ///
    /// This function is mainly useful for data that lives for the remainder of
    /// the program's life. Dropping the returned reference will cause a memory
    /// leak. If this is not acceptable, the reference should first be wrapped
    /// with the [`Box::from_raw`] function producing a `Box`. This `Box` can
    /// then be dropped which will properly destroy `T` and release the
    /// allocated memory.
    ///
    /// Note: this is an associated function, which means that you have
    /// to call it as `Box::leak(b)` instead of `b.leak()`. This
    /// is so that there is no conflict with a method on the inner type.
    #[inline]
    pub fn leak(b: Box<'a, T>) -> &'a mut T {
        unsafe { &mut *Box::into_raw(b) }
    }
}

impl<'a, T: ?Sized> Drop for Box<'a, T> {
    fn drop(&mut self) {
        unsafe {
            // `Box` owns value of `T`, but not memory behind it.
            std::ptr::drop_in_place(self.0);
        }
    }
}

impl<'a, T> Default for Box<'a, [T]> {
    fn default() -> Self {
        Self(&mut [])
    }
}

impl<'a> Default for Box<'a, str> {
    fn default() -> Self {
        unsafe {
            Box::from_raw(Box::into_raw(Box::<[u8]>::default()) as *mut str)
        }
    }
}

impl<'a, 'b, T> PartialEq<Box<'b, T>> for Box<'a, T>
where
    T: PartialEq + ?Sized,
{
    #[inline]
    fn eq(&self, other: &Box<'b, T>) -> bool {
        PartialEq::eq(&**self, &**other)
    }

    #[inline]
    fn ne(&self, other: &Box<'b, T>) -> bool {
        PartialEq::ne(&**self, &**other)
    }
}

impl<'a, 'b, T> PartialOrd<Box<'b, T>> for Box<'a, T>
where
    T: PartialOrd + ?Sized,
{
    #[inline]
    fn partial_cmp(&self, other: &Box<'b, T>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }

    #[inline]
    fn lt(&self, other: &Box<'b, T>) -> bool {
        PartialOrd::lt(&**self, &**other)
    }

    #[inline]
    fn le(&self, other: &Box<'b, T>) -> bool {
        PartialOrd::le(&**self, &**other)
    }

    #[inline]
    fn ge(&self, other: &Box<'b, T>) -> bool {
        PartialOrd::ge(&**self, &**other)
    }

    #[inline]
    fn gt(&self, other: &Box<'b, T>) -> bool {
        PartialOrd::gt(&**self, &**other)
    }
}

impl<'a, T> Ord for Box<'a, T>
where
    T: Ord + ?Sized,
{
    #[inline]
    fn cmp(&self, other: &Box<'a, T>) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

impl<'a, T> Eq for Box<'a, T> where T: Eq + ?Sized {}

impl<'a, T> Hash for Box<'a, T>
where
    T: Hash + ?Sized,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<'a, T> Hasher for Box<'a, T>
where
    T: Hasher + ?Sized,
{
    fn finish(&self) -> u64 {
        (**self).finish()
    }

    fn write(&mut self, bytes: &[u8]) {
        (**self).write(bytes)
    }

    fn write_u8(&mut self, i: u8) {
        (**self).write_u8(i)
    }

    fn write_u16(&mut self, i: u16) {
        (**self).write_u16(i)
    }

    fn write_u32(&mut self, i: u32) {
        (**self).write_u32(i)
    }

    fn write_u64(&mut self, i: u64) {
        (**self).write_u64(i)
    }

    fn write_u128(&mut self, i: u128) {
        (**self).write_u128(i)
    }

    fn write_usize(&mut self, i: usize) {
        (**self).write_usize(i)
    }

    fn write_i8(&mut self, i: i8) {
        (**self).write_i8(i)
    }

    fn write_i16(&mut self, i: i16) {
        (**self).write_i16(i)
    }

    fn write_i32(&mut self, i: i32) {
        (**self).write_i32(i)
    }

    fn write_i64(&mut self, i: i64) {
        (**self).write_i64(i)
    }

    fn write_i128(&mut self, i: i128) {
        (**self).write_i128(i)
    }

    fn write_isize(&mut self, i: isize) {
        (**self).write_isize(i)
    }
}

impl<'a, T: ?Sized> From<Box<'a, T>> for Pin<Box<'a, T>> {
    /// Converts a `Box<T>` into a `Pin<Box<T>>`
    ///
    /// This conversion does not allocate on the heap and happens in place.
    fn from(boxed: Box<'a, T>) -> Self {
        // It's not possible to move or replace the insides of a `Pin<Box<T>>`
        // when `T: !Unpin`,  so it's safe to pin it directly without any
        // additional requirements.
        unsafe { Pin::new_unchecked(boxed) }
    }
}

impl<'a> Box<'a, dyn Any> {
    #[inline]
    /// Attempt to downcast the box to a concrete type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::any::Any;
    ///
    /// fn print_if_string(value: Box<dyn Any>) {
    ///     if let Ok(string) = value.downcast::<String>() {
    ///         println!("String ({}): {}", string.len(), string);
    ///     }
    /// }
    ///
    /// let my_string = "Hello World".to_string();
    /// print_if_string(Box::new(my_string));
    /// print_if_string(Box::new(0i8));
    /// ```
    pub fn downcast<T: Any>(self) -> Result<Box<'a, T>, Box<'a, dyn Any>> {
        if self.is::<T>() {
            unsafe {
                let raw: *mut dyn Any = Box::into_raw(self);
                Ok(Box::from_raw(raw as *mut T))
            }
        } else {
            Err(self)
        }
    }
}

impl<'a> Box<'a, dyn Any + Send> {
    #[inline]
    /// Attempt to downcast the box to a concrete type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::any::Any;
    ///
    /// fn print_if_string(value: Box<dyn Any + Send>) {
    ///     if let Ok(string) = value.downcast::<String>() {
    ///         println!("String ({}): {}", string.len(), string);
    ///     }
    /// }
    ///
    /// let my_string = "Hello World".to_string();
    /// print_if_string(Box::new(my_string));
    /// print_if_string(Box::new(0i8));
    /// ```
    pub fn downcast<T: Any>(
        self,
    ) -> Result<Box<'a, T>, Box<'a, dyn Any + Send>> {
        if self.is::<T>() {
            unsafe {
                let raw: *mut (dyn Any + Send) = Box::into_raw(self);
                Ok(Box::from_raw(raw as *mut T))
            }
        } else {
            Err(self)
        }
    }
}

impl<'a, T> fmt::Display for Box<'a, T>
where
    T: fmt::Display + ?Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<'a, T> fmt::Debug for Box<'a, T>
where
    T: fmt::Debug + ?Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, T: ?Sized> fmt::Pointer for Box<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ptr: *const T = &**self;
        fmt::Pointer::fmt(&ptr, f)
    }
}

impl<'a, T: ?Sized> Deref for Box<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl<'a, T: ?Sized> DerefMut for Box<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}

impl<'a, I> Iterator for Box<'a, I>
where
    I: Iterator + ?Sized,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        (**self).next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (**self).size_hint()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        (**self).nth(n)
    }

    fn last(self) -> Option<Self::Item> {
        #[inline]
        fn some<T>(_: Option<T>, x: T) -> Option<T> {
            Some(x)
        }
        self.fold(None, some)
    }
}

impl<'a, I> DoubleEndedIterator for Box<'a, I>
where
    I: DoubleEndedIterator + ?Sized,
{
    fn next_back(&mut self) -> Option<I::Item> {
        (**self).next_back()
    }

    fn nth_back(&mut self, n: usize) -> Option<I::Item> {
        (**self).nth_back(n)
    }
}

impl<'a, I> ExactSizeIterator for Box<'a, I>
where
    I: ExactSizeIterator + ?Sized,
{
    fn len(&self) -> usize {
        (**self).len()
    }
}

impl<'a, I> FusedIterator for Box<'a, I> where I: FusedIterator + ?Sized {}

// TODO: finish `arena_vec` crate, and uncomment below:
// impl<'a, A> Box<'a, [A]> {
//     pub fn from_iter_in<T>(iter: T, a: &'a Bump) -> Self
//     where
//         T: IntoIterator<Item = A>,
//     {
//         use crate::vec_arena::Vec;
//         let mut vec = Vec::new_in(a);
//         vec.extend(iter);
//         vec.into_boxed_slice()
//     }
// }

impl<'a, T: ?Sized> borrow::Borrow<T> for Box<'a, T> {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<'a, T: ?Sized> borrow::BorrowMut<T> for Box<'a, T> {
    fn borrow_mut(&mut self) -> &mut T {
        &mut **self
    }
}

impl<'a, T: ?Sized> AsRef<T> for Box<'a, T> {
    fn as_ref(&self) -> &T {
        &**self
    }
}

impl<'a, T: ?Sized> AsMut<T> for Box<'a, T> {
    fn as_mut(&mut self) -> &mut T {
        &mut **self
    }
}

impl<'a, T: ?Sized> Unpin for Box<'a, T> {}

impl<'a, F> Future for Box<'a, F>
where
    F: Future + Unpin + ?Sized,
{
    type Output = F::Output;

    fn poll(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Self::Output> {
        F::poll(Pin::new(&mut *self), cx)
    }
}

macro_rules! array_impls {
    ($($N: expr)+) => {
        $(
            /// This impl replaces unsize coersion.
            impl<'a, T> From<Box<'a, [T; $N]>> for Box<'a, [T]> {
                fn from(mut arr: Box<'a, [T; $N]>) -> Box<'a, [T]> {
                    let ptr = core::ptr::slice_from_raw_parts_mut(arr.as_mut_ptr(), $N);
                    mem::forget(arr);
                    unsafe { Box::from_raw(ptr) }
                }
            }


            /// This impl replaces unsize coersion.
            impl<'a, T> TryFrom<Box<'a, [T]>> for Box<'a, [T; $N]> {
                type Error = Box<'a, [T]>;
                fn try_from(mut slice: Box<'a, [T]>) -> Result<Box<'a, [T; $N]>, Box<'a, [T]>> {
                    if slice.len() == $N {
                        let ptr = slice.as_mut_ptr() as *mut [T; $N];
                        mem::forget(slice);
                        Ok(unsafe { Box::from_raw(ptr) })
                    } else {
                        Err(slice)
                    }
                }
            }
        )+
    }
}

array_impls! {
     0  1  2  3  4  5  6  7  8  9
    10 11 12 13 14 15 16 17 18 19
    20 21 22 23 24 25 26 27 28 29
    30 31 32
}
