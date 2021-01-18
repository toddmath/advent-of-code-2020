use std::{
    convert::{AsMut, AsRef},
    error::Error,
    fmt,
    io::{self, BufRead, Read, Write},
    iter,
    ops::{Deref, DerefMut},
};

pub use Either::{Left, Right};

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub enum Either<L, R> {
    /// A value of type `L`.
    Left(L),
    /// A value of type `R`.
    Right(R),
}

#[macro_export]
macro_rules! either {
    ($value:expr, $pattern:pat => $result:expr) => {
        match $value {
            Either::Left($pattern) => $result,
            Either::Right($pattern) => $result,
        }
    };
}

#[macro_export]
macro_rules! try_left {
    ($expr:expr) => {
        match $expr {
            Either::Left(val) => val,
            Either::Right(err) => {
                return Either::Right(::std::convert::From::from(err))
            },
        }
    };
}

#[macro_export]
macro_rules! try_right {
    ($expr:expr) => {
        match $expr {
            Either::Left(err) => {
                return Either::Left(::std::convert::From::from(err))
            },
            Either::Right(val) => val,
        }
    };
}

impl<L, R> Either<L, R> {
    pub fn is_left(&self) -> bool {
        match *self {
            Left(_) => true,
            Right(_) => false,
        }
    }

    pub fn is_right(&self) -> bool {
        !self.is_left()
    }

    pub fn left(self) -> Option<L> {
        match self {
            Left(l) => Some(l),
            Right(_) => None,
        }
    }

    pub fn right(self) -> Option<R> {
        match self {
            Left(_) => None,
            Right(r) => Some(r),
        }
    }

    pub fn as_ref(&self) -> Either<&L, &R> {
        match *self {
            Left(ref inner) => Left(inner),
            Right(ref inner) => Right(inner),
        }
    }

    pub fn as_mut(&mut self) -> Either<&mut L, &mut R> {
        match *self {
            Left(ref mut inner) => Left(inner),
            Right(ref mut inner) => Right(inner),
        }
    }

    pub fn flip(self) -> Either<R, L> {
        match self {
            Left(l) => Right(l),
            Right(r) => Left(r),
        }
    }

    pub fn map_left<F, M>(self, f: F) -> Either<M, R>
    where
        F: FnOnce(L) -> M,
    {
        match self {
            Left(l) => Left(f(l)),
            Right(r) => Right(r),
        }
    }

    pub fn map_right<F, S>(self, f: F) -> Either<L, S>
    where
        F: FnOnce(R) -> S,
    {
        match self {
            Left(l) => Left(l),
            Right(r) => Right(f(r)),
        }
    }

    /// Apply one of two functions depending on contents, unifying their result.
    /// If the value is `Left(L)` then the first function `f` is applied; if
    /// it is `Right(R)` then the second function `g` is applied.
    pub fn either<F, G, T>(self, f: F, g: G) -> T
    where
        F: FnOnce(L) -> T,
        G: FnOnce(R) -> T,
    {
        match self {
            Left(l) => f(l),
            Right(r) => g(r),
        }
    }

    /// Like `either`, but provide some context to whichever of the
    /// functions ends up being called.
    pub fn either_with<Ctx, F, G, T>(self, ctx: Ctx, f: F, g: G) -> T
    where
        F: FnOnce(Ctx, L) -> T,
        G: FnOnce(Ctx, R) -> T,
    {
        match self {
            Left(l) => f(ctx, l),
            Right(r) => g(ctx, r),
        }
    }

    /// Apply the function `f` on the value in the `Left` variant if it is
    /// present.
    pub fn left_and_then<F, S>(self, f: F) -> Either<S, R>
    where
        F: FnOnce(L) -> Either<S, R>,
    {
        match self {
            Left(l) => f(l),
            Right(r) => Right(r),
        }
    }

    /// Apply the function `f` on the value in the `Right` variant if it is
    /// present.
    pub fn right_and_then<F, S>(self, f: F) -> Either<L, S>
    where
        F: FnOnce(R) -> Either<L, S>,
    {
        match self {
            Left(l) => Left(l),
            Right(r) => f(r),
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn into_iter(self) -> Either<L::IntoIter, R::IntoIter>
    where
        L: IntoIterator,
        R: IntoIterator<Item = L::Item>,
    {
        match self {
            Left(l) => Left(l.into_iter()),
            Right(r) => Right(r.into_iter()),
        }
    }

    pub fn left_or(self, other: L) -> L {
        match self {
            Either::Left(l) => l,
            Either::Right(_) => other,
        }
    }

    pub fn left_or_default(self) -> L
    where
        L: Default,
    {
        match self {
            Either::Left(l) => l,
            Either::Right(_) => L::default(),
        }
    }

    pub fn left_or_else<F>(self, f: F) -> L
    where
        F: FnOnce(R) -> L,
    {
        match self {
            Either::Left(l) => l,
            Either::Right(r) => f(r),
        }
    }

    pub fn right_or(self, other: R) -> R {
        match self {
            Either::Left(_) => other,
            Either::Right(r) => r,
        }
    }

    pub fn right_or_default(self) -> R
    where
        R: Default,
    {
        match self {
            Either::Left(_) => R::default(),
            Either::Right(r) => r,
        }
    }

    pub fn right_or_else<F>(self, f: F) -> R
    where
        F: FnOnce(L) -> R,
    {
        match self {
            Either::Left(l) => f(l),
            Either::Right(r) => r,
        }
    }

    pub fn unwrap_left(self) -> L
    where
        R: std::fmt::Debug,
    {
        match self {
            Either::Left(l) => l,
            Either::Right(r) => {
                panic!(
                    "called `Either::unwrap_left()` on a `Right` value: {:?}",
                    r
                )
            },
        }
    }

    pub fn unwrap_right(self) -> R
    where
        L: std::fmt::Debug,
    {
        match self {
            Either::Right(r) => r,
            Either::Left(l) => panic!(
                "called `Either::unwrap_right()` on a `Left` value: {:?}",
                l
            ),
        }
    }

    pub fn expect_left(self, msg: &str) -> L
    where
        R: std::fmt::Debug,
    {
        match self {
            Either::Left(l) => l,
            Either::Right(r) => panic!("{}: {:?}", msg, r),
        }
    }

    pub fn expect_right(self, msg: &str) -> R
    where
        L: std::fmt::Debug,
    {
        match self {
            Either::Right(r) => r,
            Either::Left(l) => panic!("{}: {:?}", msg, l),
        }
    }
}

// impl<L, R> IntoIterator for Either<L, R>
// where
//     L: IntoIterator,
//     R: IntoIterator<Item = L::Item>,
// {
//     type IntoIter = Either<L::Item, R::Item>;
//     type Item = R::Item;

//     fn into_iter(self) -> Self::IntoIter {
//         match self {
//             Left(l) => Left(l.into_iter()),
//             Right(r) => Right(r.into_iter()),
//         }
//     }
// }

impl<T, L, R> Either<(T, L), (T, R)> {
    pub fn factor_first(self) -> (T, Either<L, R>) {
        match self {
            Left((t, l)) => (t, Left(l)),
            Right((t, r)) => (t, Right(r)),
        }
    }
}

impl<T, L, R> Either<(L, T), (R, T)> {
    pub fn factor_second(self) -> (Either<L, R>, T) {
        match self {
            Left((l, t)) => (Left(l), t),
            Right((r, t)) => (Right(r), t),
        }
    }
}

impl<T> Either<T, T> {
    pub fn into_inner(self) -> T {
        either!(self, inner => inner)
    }

    pub fn map<F, M>(self, f: F) -> Either<M, M>
    where
        F: FnOnce(T) -> M,
    {
        match self {
            Left(l) => Left(f(l)),
            Right(r) => Right(f(r)),
        }
    }
}

/// Convert from `Result` to `Either` with `Ok => Right` and `Err => Left`.
impl<L, R> From<Result<R, L>> for Either<L, R> {
    fn from(r: Result<R, L>) -> Self {
        match r {
            Err(e) => Left(e),
            Ok(o) => Right(o),
        }
    }
}

#[allow(clippy::from_over_into)]
/// Convert from `Either` to `Result` with `Right => Ok` and `Left => Err`.
impl<L, R> Into<Result<R, L>> for Either<L, R> {
    fn into(self) -> Result<R, L> {
        match self {
            Left(l) => Err(l),
            Right(r) => Ok(r),
        }
    }
}

impl<L, R, A> Extend<A> for Either<L, R>
where
    L: Extend<A>,
    R: Extend<A>,
{
    fn extend<T: IntoIterator<Item = A>>(&mut self, iter: T) {
        either!(*self, ref mut inner => inner.extend(iter))
    }
}

/// `Either<L, R>` is an iterator if both `L` and `R` are iterators.
impl<L, R> Iterator for Either<L, R>
where
    L: Iterator,
    R: Iterator<Item = L::Item>,
{
    type Item = L::Item;

    fn next(&mut self) -> Option<Self::Item> {
        either!(*self, ref mut inner => inner.next())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        either!(*self, ref inner => inner.size_hint())
    }

    fn fold<Acc, G>(self, init: Acc, f: G) -> Acc
    where
        G: FnMut(Acc, Self::Item) -> Acc,
    {
        either!(self, inner => inner.fold(init, f))
    }

    fn count(self) -> usize {
        either!(self, inner => inner.count())
    }

    fn last(self) -> Option<Self::Item> {
        either!(self, inner => inner.last())
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        either!(*self, ref mut inner => inner.nth(n))
    }

    fn collect<B>(self) -> B
    where
        B: iter::FromIterator<Self::Item>,
    {
        either!(self, inner => inner.collect())
    }

    fn all<F>(&mut self, f: F) -> bool
    where
        F: FnMut(Self::Item) -> bool,
    {
        either!(*self, ref mut inner => inner.all(f))
    }
}

impl<L, R> DoubleEndedIterator for Either<L, R>
where
    L: DoubleEndedIterator,
    R: DoubleEndedIterator<Item = L::Item>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        either!(*self, ref mut inner => inner.next_back())
    }
}

impl<L, R> ExactSizeIterator for Either<L, R>
where
    L: ExactSizeIterator,
    R: ExactSizeIterator<Item = L::Item>,
{
}

/// `Either<L, R>` implements `Read` if both `L` and `R` do.
impl<L, R> Read for Either<L, R>
where
    L: Read,
    R: Read,
{
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        either!(*self, ref mut inner => inner.read(buf))
    }

    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize> {
        either!(*self, ref mut inner => inner.read_to_end(buf))
    }
}

impl<L, R> BufRead for Either<L, R>
where
    L: BufRead,
    R: BufRead,
{
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        either!(*self, ref mut inner => inner.fill_buf())
    }

    fn consume(&mut self, amt: usize) {
        either!(*self, ref mut inner => inner.consume(amt))
    }
}

/// `Either<L, R>` implements `Write` if both `L` and `R` do.
impl<L, R> Write for Either<L, R>
where
    L: Write,
    R: Write,
{
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        either!(*self, ref mut inner => inner.write(buf))
    }

    fn flush(&mut self) -> io::Result<()> {
        either!(*self, ref mut inner => inner.flush())
    }
}

impl<L, R, Target> AsRef<Target> for Either<L, R>
where
    L: AsRef<Target>,
    R: AsRef<Target>,
{
    fn as_ref(&self) -> &Target {
        either!(*self, ref inner => inner.as_ref())
    }
}

macro_rules! impl_specific_ref_and_mut {
    ($t:ty) => {
        impl<L, R> AsRef<$t> for Either<L, R>
            where L: AsRef<$t>, R: AsRef<$t>
        {
            fn as_ref(&self) -> &$t {
                either!(*self, ref inner => inner.as_ref())
            }
        }

        impl<L, R> AsMut<$t> for Either<L, R>
            where L: AsMut<$t>, R: AsMut<$t>
        {
            fn as_mut(&mut self) -> &mut $t {
                either!(*self, ref mut inner => inner.as_mut())
            }
        }
    };
}

impl_specific_ref_and_mut!(str);
impl_specific_ref_and_mut!(::std::path::Path);
impl_specific_ref_and_mut!(::std::ffi::OsStr);

impl<L, R, Target> AsRef<[Target]> for Either<L, R>
where
    L: AsRef<[Target]>,
    R: AsRef<[Target]>,
{
    fn as_ref(&self) -> &[Target] {
        either!(*self, ref inner => inner.as_ref())
    }
}

impl<L, R, Target> AsMut<Target> for Either<L, R>
where
    L: AsMut<Target>,
    R: AsMut<Target>,
{
    fn as_mut(&mut self) -> &mut Target {
        either!(*self, ref mut inner => inner.as_mut())
    }
}

impl<L, R, Target> AsMut<[Target]> for Either<L, R>
where
    L: AsMut<[Target]>,
    R: AsMut<[Target]>,
{
    fn as_mut(&mut self) -> &mut [Target] {
        either!(*self, ref mut inner => inner.as_mut())
    }
}

impl<L, R> Deref for Either<L, R>
where
    L: Deref,
    R: Deref<Target = L::Target>,
{
    type Target = L::Target;

    fn deref(&self) -> &Self::Target {
        either!(*self, ref inner => &*inner)
    }
}

impl<L, R> DerefMut for Either<L, R>
where
    L: DerefMut,
    R: DerefMut<Target = L::Target>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        either!(*self, ref mut inner => &mut *inner)
    }
}

impl<L, R> Error for Either<L, R>
where
    L: Error,
    R: Error,
{
}

impl<L, R> fmt::Display for Either<L, R>
where
    L: fmt::Display,
    R: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        either!(*self, ref inner => inner.fmt(f))
    }
}

/// A helper macro to check if AsRef and AsMut are implemented for a given
/// type.
macro_rules! check_t {
    ($t:ty) => {{
        fn check_ref<T: AsRef<$t>>() {}
        fn propagate_ref<T1: AsRef<$t>, T2: AsRef<$t>>() {
            check_ref::<Either<T1, T2>>()
        }
        fn check_mut<T: AsMut<$t>>() {}
        fn propagate_mut<T1: AsMut<$t>, T2: AsMut<$t>>() {
            check_mut::<Either<T1, T2>>()
        }
    }};
}

// This "unused" method is here to ensure that compilation doesn't fail on given
// types.
#[allow(clippy::items_after_statements)]
fn _unsized_ref_propagation() {
    check_t!(str);

    fn check_array_ref<T: AsRef<[Item]>, Item>() {}
    fn check_array_mut<T: AsMut<[Item]>, Item>() {}

    fn propagate_array_ref<T1: AsRef<[Item]>, T2: AsRef<[Item]>, Item>() {
        check_array_ref::<Either<T1, T2>, _>()
    }

    fn propagate_array_mut<T1: AsMut<[Item]>, T2: AsMut<[Item]>, Item>() {
        check_array_mut::<Either<T1, T2>, _>()
    }
}

// This "unused" method is here to ensure that compilation doesn't fail on given
// types.
fn _unsized_std_propagation() {
    check_t!(::std::path::Path);
    check_t!(::std::ffi::OsStr);
}

#[cfg(test)]
mod tests {
    use super::*;

    use Either::{Left, Right};

    #[test]
    fn basic() {
        let mut e = Left(2);
        let r = Right(2);
        assert_eq!(e, Left(2));
        e = r;
        assert_eq!(e, Right(2));
        assert_eq!(e.left(), None);
        assert_eq!(e.right(), Some(2));
        assert_eq!(e.as_ref().right(), Some(&2));
        assert_eq!(e.as_mut().right(), Some(&mut 2));
    }

    #[allow(clippy::items_after_statements)]
    #[test]
    fn macros() {
        fn a() -> Either<u32, u32> {
            let x: u32 = try_left!(Right(1337_u32));
            Left(x * 2)
        }
        assert_eq!(a(), Right(1337));

        fn b() -> Either<String, &'static str> {
            Right(try_right!(Left("foo bar")))
        }
        assert_eq!(b(), Left(String::from("foo bar")));
    }

    #[test]
    fn deref() {
        fn is_str(_: &str) {}
        let value: Either<String, &str> = Left(String::from("test"));
        is_str(&*value);
    }

    #[test]
    fn iter() {
        let x = 3;
        let mut iter = match x {
            3 => Left(0..10),
            _ => Right(17..),
        };

        assert_eq!(iter.next(), Some(0));
        assert_eq!(iter.count(), 9);
    }

    #[allow(clippy::shadow_unrelated)]
    #[test]
    fn read_write() {
        use std::io;

        let use_stdio = false;
        let mockdata = [0xff; 256];

        let mut reader = if use_stdio {
            Left(io::stdin())
        } else {
            Right(&mockdata[..])
        };

        let mut buf = [0_u8; 16];
        assert_eq!(reader.read(&mut buf).unwrap(), buf.len());
        assert_eq!(&buf, &mockdata[..buf.len()]);

        let mut mockbuf = [0_u8; 256];
        let mut writer = if use_stdio {
            Left(io::stdout())
        } else {
            Right(&mut mockbuf[..])
        };

        let buf = [1_u8; 16];
        assert_eq!(writer.write(&buf).unwrap(), buf.len());
    }

    #[test]
    #[allow(deprecated)]
    fn error() {
        let invalid_utf8 = b"\xff";
        let res = if let Err(error) = ::std::str::from_utf8(invalid_utf8) {
            Err(Left(error))
        } else if let Err(error) = "x".parse::<i32>() {
            Err(Right(error))
        } else {
            Ok(())
        };
        assert!(res.is_err());
        res.unwrap_err().description(); // make sure this can be called
    }
}
