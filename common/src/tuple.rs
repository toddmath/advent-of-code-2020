#![allow(non_snake_case)]

use num_traits::Zero;
#[allow(clippy::wildcard_imports)]
use std::{convert, fmt, mem, ops::*, ptr};

pub struct Elements<T> {
    tuple: T,
    index: usize,
}

impl<T> Elements<T> {
    #[inline]
    fn new(tuple: T) -> Self {
        Self { tuple, index: 0 }
    }
}

pub struct IntoElements<T: TupleElements> {
    tuple: Option<T>,
    index: usize,
}

impl<T: TupleElements> IntoElements<T> {
    #[inline]
    fn new(t: T) -> Self {
        Self {
            tuple: Some(t),
            index: 0,
        }
    }
}

#[allow(clippy::module_name_repetitions)]
pub unsafe trait TupleElements: Sized {
    type Element;
    const N: usize;

    #[inline]
    fn elements(&self) -> Elements<&Self> {
        Elements::new(self)
    }

    #[inline]
    fn elements_mut(&mut self) -> Elements<&mut Self> {
        Elements::new(self)
    }

    #[inline]
    fn into_elements(self) -> IntoElements<Self> {
        IntoElements::new(self)
    }

    fn get(&self, n: usize) -> Option<&Self::Element>;

    fn get_mut(&mut self, n: usize) -> Option<&mut Self::Element>;

    fn from_iter<I>(iter: I) -> Option<Self>
    where
        I: Iterator<Item = Self::Element>;
}

pub trait Map<T>: TupleElements {
    type Output: TupleElements<Element = T>;

    fn map<F>(self, f: F) -> Self::Output
    where
        F: Fn(Self::Element) -> T;

    fn map_mut<F>(self, f: F) -> Self::Output
    where
        F: FnMut(Self::Element) -> T;
}

pub trait Splat<T> {
    fn splat(value: T) -> Self;
}

pub trait Call<T> {
    type Output;
    fn call(&self, args: T) -> Self::Output;
}

pub trait CallOnce<T> {
    type Output;
    fn call_once(self, args: T) -> Self::Output;
}

pub trait CallMut<T> {
    type Output;
    fn call_mut(&mut self, args: T) -> Self::Output;
}

impl<'elems, T> Iterator for Elements<&'elems T>
where
    T: TupleElements,
{
    type Item = &'elems T::Element;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let t = self.tuple.get(self.index);
        if t.is_some() {
            self.index += 1;
        }
        t
    }
}

impl<'elems, T> Iterator for Elements<&'elems mut T>
where
    T: TupleElements,
{
    type Item = &'elems mut T::Element;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        #[allow(clippy::option_if_let_else)]
        if let Some(t) = self.tuple.get_mut(self.index) {
            self.index += 1;

            // SAFETY: we only hand one ref to each item which is tied to
            // our elems lifetime
            Some(unsafe { &mut *(t as *mut T::Element) })
        } else {
            None
        }
    }
}

impl<T> Iterator for IntoElements<T>
where
    T: TupleElements,
{
    type Item = T::Element;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        #[allow(clippy::option_if_let_else)]
        if let Some(p) = self.tuple.as_mut().unwrap().get(self.index) {
            self.index += 1;
            let v = unsafe { ptr::read(p) };
            Some(v)
        } else {
            None
        }
    }
}

impl<T> Drop for IntoElements<T>
where
    T: TupleElements,
{
    #[inline]
    fn drop(&mut self) {
        let mut tuple = self.tuple.take().unwrap();
        for i in self.index..T::N {
            unsafe {
                ptr::drop_in_place(tuple.get_mut(i).unwrap());
            }
        }
        mem::forget(tuple);
    }
}

/// Allows to join/concatenate two tuples
pub trait OpJoin<RH> {
    type Output;
    fn join(self, rhs: RH) -> Self::Output;
}

pub trait OpSplit<L> {
    type R;
    fn split(self) -> (L, Self::R);
}

pub trait OpRotateLeft {
    type Output;
    /// rotate left. The previously first element is now the first.
    fn rot_l(self) -> Self::Output;
}

pub trait OpRotateRight {
    type Output;
    /// rotate right. The previously last element is now the last.
    fn rot_r(self) -> Self::Output;
}

pub trait OpReverse {
    type Output;
    /// Reverse the elements;
    fn reverse(self) -> Self::Output;
}

#[macro_export]
macro_rules! impl_tuple {
        ($def:ident) => ($def!(
T1 A1 { A.a.0 }
T2 A2 { A.a.0, B.b.1 }
T3 A3 { A.a.0, B.b.1, C.c.2 }
T4 A4 { A.a.0, B.b.1, C.c.2, D.d.3 }
T5 A5 { A.a.0, B.b.1, C.c.2, D.d.3, E.e.4 }
T6 A6 { A.a.0, B.b.1, C.c.2, D.d.3, E.e.4, F.f.5 }
T7 A7 { A.a.0, B.b.1, C.c.2, D.d.3, E.e.4, F.f.5, G.g.6 }
T8 A8 { A.a.0, B.b.1, C.c.2, D.d.3, E.e.4, F.f.5, G.g.6, H.h.7 }
T9 A9 { A.a.0, B.b.1, C.c.2, D.d.3, E.e.4, F.f.5, G.g.6, H.h.7, I.i.8 }
T10 A10 { A.a.0, B.b.1, C.c.2, D.d.3, E.e.4, F.f.5, G.g.6, H.h.7, I.i.8, J.j.9 }
T11 A11 { A.a.0, B.b.1, C.c.2, D.d.3, E.e.4, F.f.5, G.g.6, H.h.7, I.i.8, J.j.9, K.k.10 }
T12 A12 { A.a.0, B.b.1, C.c.2, D.d.3, E.e.4, F.f.5, G.g.6, H.h.7, I.i.8, J.j.9, K.k.10, L.l.11 }
T13 A13 { A.a.0, B.b.1, C.c.2, D.d.3, E.e.4, F.f.5, G.g.6, H.h.7, I.i.8, J.j.9, K.k.10, L.l.11, M.m.12 }
T14 A14 { A.a.0, B.b.1, C.c.2, D.d.3, E.e.4, F.f.5, G.g.6, H.h.7, I.i.8, J.j.9, K.k.10, L.l.11, M.m.12, N.n.13 }
T15 A15 { A.a.0, B.b.1, C.c.2, D.d.3, E.e.4, F.f.5, G.g.6, H.h.7, I.i.8, J.j.9, K.k.10, L.l.11, M.m.12, N.n.13, O.o.14 }
T16 A16 { A.a.0, B.b.1, C.c.2, D.d.3, E.e.4, F.f.5, G.g.6, H.h.7, I.i.8, J.j.9, K.k.10, L.l.11, M.m.12, N.n.13, O.o.14, P.p.15 }
        );)
    }

macro_rules! init {
    ($( $tuple:ident $arr:ident { $( $ty:ident . $t:ident . $idx:tt ),* } )*) => {
        $(
            pub struct $tuple<$( $ty ),*>($( pub $ty ),*);
            pub type $arr<T> = $tuple<$( A!(T, $ty) ),*>;
        )*
    };
}

impl_tuple!(init);

pub fn tuple<T, I>(iter: I) -> Option<T>
where
    T: TupleElements,
    I: Iterator<Item = T::Element>,
{
    T::from_iter(iter)
}

macro_rules! m_init {
    ($($tuple:ident $Arr:ident { $($T:ident . $t:ident . $idx:tt),* } )*) => {
        $(
            impl<$($T),*> $tuple<$($T),*> {
                pub fn as_refs(&self) -> $tuple<$(&$T),*> {
                    $tuple( $( &self.$idx ),* )
                }
                pub fn as_mut_refs(&mut self) -> $tuple<$(&mut $T),*> {
                    $tuple( $( &mut self.$idx ),* )
                }
            }
            impl<$($T),*> Clone for $tuple<$($T),*> where $( $T: Clone ),* {
                #[inline(always)]
                fn clone(&self) -> Self {
                    $tuple( $( self.$idx.clone() ),* )
                }
            }
            impl<$($T),*> Copy for $tuple<$($T),*> where $( $T: Copy ),* {}

            impl<$($T),*> PartialEq for $tuple<$($T),*> where $( $T: PartialEq ),* {
                #[inline(always)]
                fn eq(&self, other: &Self) -> bool {
                    $( self.$idx == other.$idx)&&*
                }
            }
            impl<$($T),*> Eq for $tuple<$($T),*> where $( $T: Eq ),* {}
            impl<$($T),*> fmt::Debug for $tuple<$($T),*> where $( $T: fmt::Debug ),* {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    f.debug_tuple(stringify!($tuple))
                    $( .field(&self.$idx) )*
                    .finish()
                }
            }
            impl<$($T),*> Default for $tuple<$($T),*> where $( $T: Default ),* {
                #[inline(always)]
                fn default() -> Self {
                    $tuple( $( $T::default() ),* )
                }
            }
            impl<$($T),*> From<u16> for $tuple<$($T),*> where $( $T: From<u16> ),* {
                #[inline(always)]
                fn from(value: u16) -> Self {
                    $tuple( $( $T::from(value) ),* )
                }
            }
        )*
    };
}

impl_tuple!(m_init);

macro_rules! m_tuple {
    ($($Tuple:ident $Arr:ident { $($T:ident . $t:ident . $idx:tt),* } )*) => {
        $(
            #[allow(unused_parens)]
            impl<$($T),*> $Tuple<$(Option<$T>),*> {
                pub fn collect(self) -> Option< $Tuple<$($T),*> > {
                    match self {
                        $Tuple( $( Some($T) ),* ) => Some( $Tuple( $( $T ),* ) ),
                        _ => None
                    }
                }
            }
            #[allow(unused_parens)]
            unsafe impl<T> TupleElements for $Tuple<$(A!(T,$T),)*> {
                type Element = T;
                const N: usize = $(a!(1, $idx)+)* 0;
                #[inline(always)]
                fn get(&self, index: usize) -> Option<&T> {
                    match index {
                    $( $idx => Some(&self.$idx), )*
                        _ => None
                    }
                }
                #[inline(always)]
                fn get_mut(&mut self, index: usize) -> Option<&mut T> {
                    match index {
                    $( $idx => Some(&mut self.$idx), )*
                        _ => None
                    }
                }
                #[inline(always)]
                fn from_iter<I>(mut iter: I) -> Option<Self> where I: Iterator<Item=Self::Element> {
                $( let $T = match iter.next() {
                        Some(v) => v,
                        None => return None
                    }; )*
                    Some($Tuple($($T),*))
                }
            }
            #[allow(unused_parens)]
            impl<T> Splat<T> for $Tuple<$(A!(T,$T),)*> where T: Clone {
                #[inline(always)]
                fn splat(t: T) -> Self {
                    $Tuple( $( a!(t.clone(), $T) ),* )
                }
            }
            #[allow(unused_parens)]
            impl<T, U> Map<U> for $Tuple<$(A!(T,$T)),*> {
                type Output = $Tuple<$(A!(U,$T)),*>;
                #[inline(always)]
                fn map<F>(self, f: F) -> Self::Output where F: Fn(T) -> U {
                    $Tuple($(f(self.$idx)),*)
                }
                #[inline(always)]
                fn map_mut<F>(self, mut f: F) -> Self::Output where F: FnMut(T) -> U {
                    $Tuple($(f(self.$idx)),*)
                }

            }
            #[allow(unused_parens)]
            unsafe impl<T> TupleElements for ($(A!(T,$T),)*) {
                type Element = T;
                const N: usize = $(a!(1, $idx)+)* 0;
                #[inline(always)]
                fn get(&self, index: usize) -> Option<&T> {
                    match index {
                    $( $idx => Some(&self.$idx), )*
                        _ => None
                    }
                }
                #[inline(always)]
                fn get_mut(&mut self, index: usize) -> Option<&mut T> {
                    match index {
                    $( $idx => Some(&mut self.$idx), )*
                        _ => None
                    }
                }
                #[inline(always)]
                fn from_iter<I>(mut iter: I) -> Option<Self> where I: Iterator<Item=Self::Element> {
                $( let $T = match iter.next() {
                        Some(v) => v,
                        None => return None
                    }; )*
                    Some(($($T,)*))
                }
            }
            #[allow(unused_parens)]
            impl<T> Splat<T> for ($(A!(T,$T),)*) where T: Clone {
                #[inline(always)]
                fn splat(t: T) -> Self {
                    ( $( a!(t.clone(), $T), )* )
                }
            }
            #[allow(unused_parens)]
            impl<T, U> Map<U> for ($(A!(T,$T),)*) {
                type Output = ($(A!(U,$T),)*);
                #[inline(always)]
                fn map<F>(self, f: F) -> Self::Output where F: Fn(T) -> U {
                    ($(f(self.$idx),)*)
                }
                #[inline(always)]
                fn map_mut<F>(self, mut f: F) -> Self::Output where F: FnMut(T) -> U {
                    ($(f(self.$idx),)*)
                }
            }
            #[allow(unused_parens)]
            impl<$($T),*> OpRotateLeft for $Tuple<$($T),*> {
                type Output = Rot_l!(x_ty_ident, $Tuple; $($T,)*);
                #[inline(always)]
                fn rot_l(self) -> Self::Output {
                    rot_l!(x_ty_expr, $Tuple; $(self.$idx,)*)
                }
            }
            #[allow(unused_parens)]
            impl<$($T),*> OpRotateLeft for ($($T,)*) {
                type Output = Rot_l!(x_tuple_ident; $($T,)*);
                #[inline(always)]
                fn rot_l(self) -> Self::Output {
                    rot_l!(x_tuple_expr; $(self.$idx,)*)
                }
            }
            #[allow(unused_parens)]
            impl<$($T),*> OpRotateRight for $Tuple<$($T),*> {
                type Output = Rot_r!(x_ty_ident, $Tuple; $($T,)*);
                #[inline(always)]
                fn rot_r(self) -> Self::Output {
                    rot_r!(x_ty_expr, $Tuple; $(self.$idx,)*)
                }
            }
            #[allow(unused_parens)]
            impl<$($T),*> OpRotateRight for ($($T,)*) {
                type Output = Rot_r!(x_tuple_ident; $($T,)*);
                #[inline(always)]
                fn rot_r(self) -> Self::Output {
                    rot_r!(x_tuple_expr; $(self.$idx,)*)
                }
            }
            #[allow(unused_parens)]
            impl<$($T),*> OpReverse for $Tuple<$($T),*> {
                type Output = Rev!(x_ty_ident, $Tuple; $($T,)*);
                #[inline(always)]
                fn reverse(self) -> Self::Output {
                    rev!(x_ty_expr, $Tuple; $(self.$idx,)*)
                }
            }
            #[allow(unused_parens)]
            impl<$($T),*> OpReverse for ($($T,)*) {
                type Output = Rev!(x_tuple_ident; $($T,)*);
                #[inline(always)]
                fn reverse(self) -> Self::Output {
                    rev!(x_tuple_expr; $(self.$idx,)*)
                }
            }
        )*
    }
}

macro_rules! impl_join {
    ( $( $L:ident ( $( $l:ident ),* ) | $R:ident ( $( $r:ident ),* )
        => $O:ident ( $( $o:ident ),* ) )*
    ) => {
        $(
            #[allow(non_camel_case_types)]
            impl<$($l,)* $($r),*> OpJoin<$R<$($r),*>> for $L<$($l),*> {
                type Output = $O<$($l,)* $($r),*>;
                #[inline(always)]
                fn join(self, rhs: $R<$($r),*>) -> Self::Output {
                    let $L($($l),*) = self;
                    let $R($($r),*) = rhs;
                    $O($($l,)* $($r),*)
                }
            }
            #[allow(non_camel_case_types)]
            impl<$($l,)* $($r),*> OpJoin<($($r,)*)> for ($($l,)*) {
                type Output = ($($l,)* $($r),*);
                #[inline(always)]
                fn join(self, rhs: ($($r,)*)) -> Self::Output {
                    let ($($l,)*) = self;
                    let ($($r,)*) = rhs;
                    ($($l,)* $($r,)*)
                }
            }
            #[allow(non_camel_case_types)]
            impl<$($l,)* $($r),*> OpSplit<$L<$($l),*>> for $O<$($l,)* $($r),*> {
                type R = $R<$($r),*>;
                #[inline(always)]
                fn split(self) -> ($L<$($l),*>, Self::R) {
                    let $O($($l,)* $($r),*) = self;
                    ( $L($($l),*), $R($($r),*) )
                }
            }
            #[allow(non_camel_case_types, unused_parens)]
            impl<$($l,)* $($r),*> OpSplit<($($l),*)> for ($($l,)* $($r),*) {
                type R = ($($r),*);
                #[inline(always)]
                fn split(self) -> (($($l),*), Self::R) {
                    let ($($l,)* $($r),*) = self;
                    ( ($($l),*), ($($r),*) )
                }
            }
        )*
    }
}

#[allow(non_camel_case_types)]
macro_rules! m_join {
    () => {
        #[allow(non_snake_case)]
        impl_join!(
            T1(a) | T1(b) => T2(a, b)
            T1(a) | T2(b, c) => T3(a, b, c)
            T1(a) | T3(b, c, d) => T4(a, b, c, d)
            T1(a) | T4(b, c, d, e) => T5(a, b, c, d, e)
            T1(a) | T5(b, c, d, e, f) => T6(a, b, c, d, e, f)
            T1(a) | T6(b, c, d, e, f, g) => T7(a, b, c, d, e, f, g)
            T1(a) | T7(b, c, d, e, f, g, h) => T8(a, b, c, d, e, f, g, h)
            T2(a, b) | T1(c) => T3(a, b, c)
            T2(a, b) | T2(c, d) => T4(a, b, c, d)
            T2(a, b) | T3(c, d, e) => T5(a, b, c, d, e)
            T2(a, b) | T4(c, d, e, f) => T6(a, b, c, d, e, f)
            T2(a, b) | T5(c, d, e, f, g) => T7(a, b, c, d, e, f, g)
            T2(a, b) | T6(c, d, e, f, g, h) => T8(a, b, c, d, e, f, g, h)
            T3(a, b, c) | T1(d) => T4(a, b, c, d)
            T3(a, b, c) | T2(d, e) => T5(a, b, c, d, e)
            T3(a, b, c) | T3(d, e, f) => T6(a, b, c, d, e, f)
            T3(a, b, c) | T4(d, e, f, g) => T7(a, b, c, d, e, f, g)
            T3(a, b, c) | T5(d, e, f, g, h) => T8(a, b, c, d, e, f, g, h)
            T4(a, b, c, d) | T1(e) => T5(a, b, c, d, e)
            T4(a, b, c, d) | T2(e, f) => T6(a, b, c, d, e, f)
            T4(a, b, c, d) | T3(e, f, g) => T7(a, b, c, d, e, f, g)
            T4(a, b, c, d) | T4(e, f, g, h) => T8(a, b, c, d, e, f, g, h)
            T5(a, b, c, d, e) | T1(f) => T6(a, b, c, d, e, f)
            T5(a, b, c, d, e) | T2(f, g) => T7(a, b, c, d, e, f, g)
            T5(a, b, c, d, e) | T3(f, g, h) => T8(a, b, c, d, e, f, g, h)
            T6(a, b, c, d, e, f) | T1(g) => T7(a, b, c, d, e, f, g)
            T6(a, b, c, d, e, f) | T2(g, h) => T8(a, b, c, d, e, f, g, h)
            T7(a, b, c, d, e, f, g) | T1(h) => T8(a, b, c, d, e, f, g, h)
        );
    }
}

#[allow(non_camel_case_types, non_snake_case)]
impl_tuple!(m_tuple);

#[allow(non_camel_case_types)]
m_join!();

macro_rules! m_iter {
    ($($Tuple:ident $Arr:ident { $($T:ident . $t:ident . $idx:tt),* } )*) => {
        $(
            impl<$($T),*> Iterator for $Tuple<$($T),*> where $( $T: Iterator  ),* {
                type Item = $Tuple<$($T::Item),*>;
                #[allow(non_snake_case)]
                #[inline(always)]
                fn next(&mut self) -> Option<Self::Item> {
                    match ( $(self.$idx.next(), )* ) {
                        ( $( Some($T) ,)* ) => Some($Tuple( $($T),* )),
                        _ => None
                    }
                }
            }
        )*
    }
}

impl_tuple!(m_iter);

macro_rules! m_convert {
    ($($Tuple:ident $Arr:ident { $($T:ident . $t:ident . $idx:tt),* } )*) => {
        $(
            impl<$($T),*> convert::From<($($T,)*)> for $Tuple<$($T),*> {
                #[inline(always)]
                fn from(t: ($($T,)*)) -> Self {
                    $Tuple( $( t.$idx ),* )
                }
            }
            #[allow(clippy::from_over_into)]
            impl<$($T),*> convert::Into<($($T,)*)> for $Tuple<$($T),*> {
                #[inline(always)]
                fn into(self) -> ($($T,)*) {
                    ( $( self.$idx, )* )
                }
            }

            /// This is only avaible with the 'nightly' feature
            impl<T> convert::From<[T; $(a!(1, $idx)+)* 0]> for $Tuple<$(A!(T, $T)),*> {
                #[inline(always)]
                fn from(t: [T; $(a!(1, $idx)+)* 0]) -> Self {
                    // #[cfg(feature="nightly")]
                    {
                        let [$($T),*] = { t };
                        $Tuple( $( $T, )* )
                    }
                    // #[cfg(not(feature="nightly"))]
                    // unsafe {
                    //     use core::ptr;
                    //     use core::mem;
                    //     let tuple = $Tuple( $( ptr::read(&t[$idx]), )* );
                    //     mem::forget(t);
                    //     tuple
                    // }
                }
            }

            #[allow(clippy::from_over_into)]
            impl<T> convert::Into<[T; 0 $(+ a!(1, $idx))*]> for $Tuple<$(A!(T, $T)),*> {
                #[inline(always)]
                fn into(self) -> [T; 0 $(+ a!(1, $idx))*] {
                    let $Tuple($($T),*) = self;
                    [ $($T),* ]
                }
            }
            impl<'a, T> $Tuple<$(A!(T, $T)),*> where T: Clone {
                #[inline(always)]
                pub fn from_slice(slice: &'a [T]) -> Option<Self> {
                    const N: usize = $(a!(1, $idx)+)* 0;
                    if slice.len() >= N {
                        Some($Tuple( $( slice[$idx].clone() ),* ))
                    } else {
                        None
                    }
                }
            }
        )*
    }
}

impl_tuple!(m_convert);

macro_rules! m_num {
    ($($Tuple:ident $Arr:ident { $($T:ident . $t:ident . $idx:tt),* } )*) => ($(
        impl<$($T),*> Zero for $Tuple<$($T),*> where $( $T: Zero ),* {
            #[inline(always)]
            fn zero() -> Self {
                $Tuple( $( $T::zero() ),* )
            }
            #[inline(always)]
            fn is_zero(&self) -> bool {
                $( self.$idx.is_zero() )&&*
            }
        }
    )*)
}

impl_tuple!(m_num);

macro_rules! m_ops_base {
    ( $Tuple:ident { $($T:ident .$t:ident . $idx:tt),* } : $op:ident . $fn:ident ) =>
    (
        impl<$($T),*> $op for $Tuple<$($T),*> where $( $T: $op ),* {
            type Output = $Tuple<$($T::Output),*>;
            #[inline(always)]
            fn $fn(self, rhs: Self) -> Self::Output {
                $Tuple( $(self.$idx.$fn( rhs.$idx ) ),* )
            }
        }
        impl<T> $op<T> for $Tuple<$(A!(T, $T)),*> where T: $op + Clone {
            type Output = $Tuple<$(<A!(T, $T) as $op>::Output),*>;
            #[inline(always)]
            fn $fn(self, rhs: T) -> Self::Output {
                $Tuple( $(self.$idx.$fn( rhs.clone() ) ),* )
            }
        }
    )
}
macro_rules! m_ops_base_assign {
    ( $Tuple:ident { $($T:ident .$t:ident . $idx:tt),* } : $op:ident . $fn:ident ) =>
    (
        impl<$($T),*> $op for $Tuple<$($T),*> where $( $T: $op ),* {
            #[inline(always)]
            fn $fn(&mut self, rhs: Self) {
                $( self.$idx.$fn(rhs.$idx); )*
            }
        }
        impl<T> $op<T> for $Tuple<$(A!(T, $T)),*> where T: $op + Clone {
            #[inline(always)]
            fn $fn(&mut self, rhs: T) {
                $( self.$idx.$fn(rhs.clone()); )*
            }
        }
    )
}
macro_rules! m_ops_all {
    ( $Tuple:ident { $($T:ident . $t:ident . $idx:tt),* } :
        $op:ident.$fn:ident, $op_a:ident.$fn_a:ident) =>
    (
        m_ops_base!( $Tuple { $($T . $t . $idx),* } : $op.$fn );
        m_ops_base_assign!( $Tuple { $($T . $t . $idx),* } : $op_a.$fn_a );
    )
}
macro_rules! m_ops {
    ($($Tuple:ident $Arr:ident { $($T:ident . $t:ident . $idx:tt),* } )*) => ($(
        m_ops_all!( $Tuple { $($T . $t . $idx),* } : Add.add, AddAssign.add_assign );
        m_ops_all!( $Tuple { $($T . $t . $idx),* } : Sub.sub, SubAssign.sub_assign );
        m_ops_all!( $Tuple { $($T . $t . $idx),* } : Mul.mul, MulAssign.mul_assign );
        m_ops_all!( $Tuple { $($T . $t . $idx),* } : Div.div, DivAssign.div_assign );

        impl<$($T),*> Neg for $Tuple<$($T),*> where $( $T: Neg ),* {
            type Output = $Tuple<$($T::Output),*>;
            #[inline(always)]
            fn neg(self) -> Self::Output {
                $Tuple( $(self.$idx.neg()),* )
            }
        }
        impl<T> Index<usize> for $Tuple<$(A!(T,$T)),*> {
            type Output = T;
            #[inline(always)]
            fn index(&self, index: usize) -> &T {
                match index {
                    $( $idx => &self.$idx, )*
                    _ => panic!("index {} out of bounds. len is {}.", index, Self::N)
                }
            }
        }
        impl<T> IndexMut<usize> for $Tuple<$(A!(T,$T)),*> {
            #[inline(always)]
            fn index_mut(&mut self, index: usize) -> &mut T {
                match index {
                    $( $idx => &mut self.$idx, )*
                    _ => panic!("index {} out of bounds. len is {}.", index, Self::N)
                }
            }
        }
    )*)
}

impl_tuple!(m_ops);

macro_rules! m_call {
    ($($Tuple:ident $Arr:ident { $($T:ident . $t:ident . $idx:tt),* } )*) => ($(
        impl<Func, Out, $($T),*> Call<$Tuple<$($T),*>> for Func where Func: Fn($($T),*) -> Out {
            type Output = Out;
            fn call(&self, $Tuple($($t),*): $Tuple<$($T),*>) -> Out {
                self($($t),*)
            }
        }
        impl<Func, Out, $($T),*> CallMut<$Tuple<$($T),*>> for Func where Func: FnMut($($T),*) -> Out {
            type Output = Out;
            fn call_mut(&mut self, $Tuple($($t),*): $Tuple<$($T),*>) -> Out {
                self($($t),*)
            }
        }
        impl<Func, Out, $($T),*> CallOnce<$Tuple<$($T),*>> for Func where Func: FnOnce($($T),*) -> Out {
            type Output = Out;
            fn call_once(self, $Tuple($($t),*): $Tuple<$($T),*>) -> Out {
                self($($t),*)
            }
        }
        impl<Func, Out, $($T),*> Call<($($T,)*)> for Func where Func: Fn($($T),*) -> Out {
            type Output = Out;
            fn call(&self, ($($t,)*): ($($T,)*)) -> Out {
                self($($t),*)
            }
        }
        impl<Func, Out, $($T),*> CallMut<($($T,)*)> for Func where Func: FnMut($($T),*) -> Out {
            type Output = Out;
            fn call_mut(&mut self, ($($t,)*): ($($T,)*)) -> Out {
                self($($t),*)
            }
        }
        impl<Func, Out, $($T),*> CallOnce<($($T,)*)> for Func where Func: FnOnce($($T),*) -> Out {
            type Output = Out;
            fn call_once(self, ($($t,)*): ($($T,)*)) -> Out {
                self($($t),*)
            }
        }
        impl<$($T),*> ::std::hash::Hash for $Tuple<$($T),*> where $($T: ::std::hash::Hash),* {
            fn hash<HA: ::std::hash::Hasher>(&self, state: &mut HA) {
                $(
                    self.$idx.hash(state);
                )*
            }
        }
    )*)
}

impl_tuple!(m_call);

macro_rules! m_array {
    ($($Tuple:ident $Arr:ident { $($T:ident . $t:ident . $idx:tt),* } )*) => {
        $(
            unsafe impl<T> TupleElements for [T; $(a!(1, $idx)+)* 0] {
                type Element = T;
                const N: usize = $(a!(1, $idx)+)* 0;
                #[inline(always)]
                fn elements(&self) -> Elements<&Self> {
                    Elements::new(self)
                }
                #[inline(always)]
                fn elements_mut(&mut self) -> Elements<&mut Self> {
                    Elements::new(self)
                }
                #[inline(always)]
                fn into_elements(self) -> IntoElements<Self> {
                    IntoElements::new(self)
                }
                #[inline(always)]
                fn get(&self, index: usize) -> Option<&T> {
                    if index < Self::N {
                        Some(&self[index])
                    } else {
                        None
                    }
                }
                #[inline(always)]
                fn get_mut(&mut self, index: usize) -> Option<&mut T> {
                    if index < Self::N {
                        Some(&mut self[index])
                    } else {
                        None
                    }
                }
                #[inline(always)]
                fn from_iter<I>(mut iter: I) -> Option<Self> where I: Iterator<Item=Self::Element> {
                $( let $T = match iter.next() {
                        Some(v) => v,
                        None => return None
                    }; )*
                    Some([$($T,)*])
                }
            }
            impl<T> Splat<T> for [T; $(a!(1, $idx)+)* 0] where T: Clone {
                #[inline(always)]
                fn splat(t: T) -> Self {
                    [$(a!(t.clone(), $idx)),*]
                }
            }

            /// This is only avaible with the 'nightly' feature
            impl<T, U> Map<U> for [T; $(a!(1, $idx)+)* 0] {
                type Output = [U; $(a!(1, $idx)+)* 0];
                #[inline(always)]
                fn map<F>(self, f: F) -> Self::Output where F: Fn(T) -> U {
                    let [$($t),*] = { self };
                    [$(f($t)),*]
                }
                #[inline(always)]
                fn map_mut<F>(self, mut f: F) -> Self::Output where F: FnMut(T) -> U {
                    let [$($t),*] = { self };
                    [$(f($t)),*]
                }
            }
        )*
    }
}

#[allow(non_snake_case, non_camel_case_types)]
impl_tuple!(m_array);
