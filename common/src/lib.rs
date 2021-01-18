#![allow(incomplete_features)]
#![feature(
    untagged_unions,
    allocator_api,
    const_generics,
    const_in_array_repeat_expressions,
    maybe_uninit_uninit_array,
    const_fn
)]
#![warn(clippy::all, clippy::pedantic)]
#![allow(clippy::missing_errors_doc, clippy::missing_safety_doc)]

#[macro_use]
pub mod utils;
pub mod console;
pub mod either;
pub mod iter;
pub mod num;
pub mod owning_ref;
pub mod parse;
pub mod smallvec;
pub mod tuple;
// pub mod arena;
// pub mod box_arena;
// pub mod vec_arena;

pub use either::{Either, Left, Right};
pub use iter::*;
pub use num::*;
pub use parse::*;
use rayon::prelude::*;
pub use smallvec::{Array, SmallVec, ToSmallVec};
use std::sync::{
    atomic::{AtomicUsize, Ordering as AtomicOrdering},
    Mutex,
};
pub use tuple::{tuple, TupleElements};

use fnv::FnvBuildHasher;

pub type HashMap<K, V> = std::collections::HashMap<K, V, FnvBuildHasher>;
pub type HashSet<T> = std::collections::HashSet<T, FnvBuildHasher>;

pub struct Unpeekable<T>
where
    T: Iterator,
{
    pub iterator: T,
    pub last: Option<<T as Iterator>::Item>,
}

impl<T> Unpeekable<T>
where
    T: Iterator,
{
    pub fn new(iterator: T) -> Self {
        Self {
            iterator,
            last: None,
        }
    }

    pub fn unpeek(&mut self, last: <T as Iterator>::Item) {
        if self.last.is_some() {
            panic!()
        }
        self.last = Some(last);
    }
}

impl<T> Iterator for Unpeekable<T>
where
    T: Iterator,
{
    type Item = <T as Iterator>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(last) = self.last.take() {
            return Some(last);
        }
        self.iterator.next()
    }
}

pub fn quick_sort<T: PartialOrd + Send + Sync>(v: &mut [T])
where
    [T]: Copy,
{
    if v.len() <= 1 {
        return;
    }

    let mid = partition(v);
    let (lo, hi) = v.split_at_mut(mid);
    rayon::join(|| quick_sort(lo), || quick_sort(hi));
}

pub fn partition<T: PartialOrd + Send>(v: &mut [T]) -> usize
where
    [T]: Copy,
{
    let pivot = v.len() - 1;
    let mut i = 0;
    // let w = v;

    (0..pivot).for_each(|j| {
        if v[j] <= v[pivot] {
            v.swap(i, j);
            i += 1;
        }
    });

    v.swap(i, pivot);
    i
}

pub fn par_partition<T: PartialOrd + Send + Sync>(v: &mut [T]) -> usize {
    let pivot = v.len() - 1;
    let v = Mutex::new(v);
    let i = AtomicUsize::new(0);

    (0..pivot).into_par_iter().for_each(|j| {
        let mut v = v.lock().unwrap();
        if v[j] <= v[pivot] {
            let ii = i.load(AtomicOrdering::Acquire);
            v.swap(ii, j);
            i.fetch_add(1, AtomicOrdering::AcqRel);
            // i += 1;
        }
    });

    let mut v = v.lock().unwrap();
    let i = i.load(AtomicOrdering::Acquire);
    v.swap(i, pivot);
    i
}
