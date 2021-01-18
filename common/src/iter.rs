use std::{
    iter::{FusedIterator, Iterator},
    mem::MaybeUninit,
};

/// An iterator that returns k-length combinations of values from `iter`.
///
/// This `struct` is created by the `combinations` method on `IterExt`. See
/// its documentation for more.
#[derive(Debug, Clone)]
#[must_use = "iterator adaptors are lazy and do nothing unless consummed"]
pub struct Combinations<I, const K: usize>
where
    I: Iterator,
    I::Item: Clone,
{
    iter: I,
    buffer: Vec<I::Item>,
    indices: [usize; K],
    first: bool,
}

impl<I, const K: usize> Combinations<I, K>
where
    I: Iterator,
    I::Item: Clone,
{
    pub fn new(iter: I) -> Self {
        // Prepare the indices.
        let mut indices = [0; K];

        // NOTE: this clippy attribute can be removed once we can `collect` into
        // `[usize; K]`. #[allow(clippy::clippy::needless_range_loop)]
        // for i in 0..K {
        //     indices[i] = i;
        // }

        (0..K).for_each(|i| indices[i] = i);

        Self {
            buffer: vec![],
            indices,
            first: true,
            iter,
        }
    }
}

impl<I, const K: usize> Iterator for Combinations<I, K>
where
    I: Iterator,
    I::Item: Clone,
{
    type Item = [I::Item; K];

    fn next(&mut self) -> Option<Self::Item> {
        if self.first {
            // Fill the buffer for the first combination
            self.buffer.reserve(K - self.buffer.len());
            while self.buffer.len() < K {
                match self.iter.next() {
                    Some(x) => self.buffer.push(x),
                    None => return None,
                }
            }
            self.first = false;
        } else if K == 0 {
            // This check is separated, because in case of K == 0 we still
            // need to return a single empty array before returning None.
            return None;
        } else {
            // Check if we need to consume more from the iterator
            if self.indices[0] == self.buffer.len() - K {
                // Exhausted all combinations in the current buffer
                match self.iter.next() {
                    Some(x) => self.buffer.push(x),
                    None => return None,
                }
            }

            let mut i = 0;
            // Reset consecutive indices
            while i < K - 1 && self.indices[i] + 1 == self.indices[i + 1] {
                self.indices[i] = i;
                i += 1;
            }

            // Increment the last consecutive index
            self.indices[i] += 1;
        }

        // Create the result array based on the indices
        let mut out = MaybeUninit::uninit_array::<K>();
        self.indices.iter().enumerate().for_each(|(oi, i)| {
            out[oi] = MaybeUninit::new(self.buffer[*i].clone());
        });
        Some(unsafe { out.as_ptr().cast::<[I::Item; K]>().read() })
    }
}

// ! If the bounds change, make sure to change `FusedIterator for Permutations`
impl<I, const K: usize> FusedIterator for Combinations<I, K>
where
    I: FusedIterator,
    I::Item: Clone,
{
}

#[derive(Debug, Clone)]
struct FullPermutations<T, const N: usize> {
    items: [T; N],
    indices: [usize; N],
    first: bool,
    done: bool,
}

impl<T, const N: usize> FullPermutations<T, N> {
    fn new(items: [T; N]) -> Self {
        Self {
            items,
            indices: [0; N],
            first: true,
            done: false,
        }
    }
}

impl<T, const N: usize> Iterator for FullPermutations<T, N>
where
    T: Clone,
{
    type Item = [T; N];

    fn next(&mut self) -> Option<Self::Item> {
        // Iterative version of Heap's algo
        // https://en.wikipedia.org/wiki/Heap%27s_algorithm
        if self.first {
            self.first = false;
        } else if self.done {
            return None;
        } else {
            let mut i = 1;
            while i < N && self.indices[i] >= i {
                self.indices[i] = 0;
                i += 1;
            }

            if i >= N {
                self.done = true;
                return None;
            }

            if i & 1 == 0 {
                self.items.swap(i, 0);
            } else {
                self.items.swap(i, self.indices[i]);
            };

            self.indices[i] += 1;
        }

        Some(self.items.clone())
    }
}

/// An iterator that returns k-length permutations of values from `iter`.
///
/// This `struct` is created by the `permutations` method on `IterExt`. See
/// its documentation for more.
#[derive(Debug, Clone)]
#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
pub struct Permutations<I, const K: usize>
where
    I: Iterator,
    I::Item: Clone,
{
    iter: Combinations<I, K>,
    perm_iter: Option<FullPermutations<I::Item, K>>,
}

impl<I, const K: usize> Iterator for Permutations<I, K>
where
    I: Iterator,
    I::Item: Clone,
{
    type Item = [I::Item; K];

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(perm_iter) = &mut self.perm_iter {
            if let Some(a) = perm_iter.next() {
                return Some(a);
            }
        }

        self.perm_iter = self.iter.next().map(FullPermutations::new);
        // Each `FullPermutations` is guaranteed to return at least one item.
        // `None` will be returned only if `perm_iter` is `None`,
        // which means that the inner iterator returned `None`.
        self.perm_iter.as_mut().and_then(Iterator::next)
    }
}

impl<I, const K: usize> Permutations<I, K>
where
    I: Iterator,
    I::Item: Clone,
{
    pub fn new(iter: I) -> Self {
        Self {
            iter: Combinations::new(iter),
            perm_iter: None,
        }
    }
}

impl<I, const K: usize> FusedIterator for Permutations<I, K>
where
    I: FusedIterator,
    I::Item: Clone,
{
}

/// An extension trait adding `combinations` and `permutations` to `Iterator`.
#[allow(clippy::module_name_repetitions)]
pub trait IterExt: Iterator + Sized
where
    Self::Item: Clone,
{
    /// Return an iterator adaptor that iterates over the k-length combinations
    /// of the elements from an iterator.
    ///
    /// The iterator produces a new array per iteration, and clones the iterator
    /// elements. If `K` is greater than the length of the input iterator the
    /// resulting iterator adaptor will yield no items.
    ///
    /// # Examples
    ///
    /// ```
    /// use common::IterExt;
    ///
    /// let mut combinations = (1..5).combinations();
    /// assert_eq!(combinations.next(), Some([1, 2, 3]));
    /// assert_eq!(combinations.next(), Some([1, 2, 4]));
    /// assert_eq!(combinations.next(), Some([1, 3, 4]));
    /// assert_eq!(combinations.next(), Some([2, 3, 4]));
    /// assert_eq!(combinations.next(), None);
    /// ```
    ///
    /// Note: Combinations does not take into account the equality of the
    /// iterated values.
    ///
    /// ```
    /// # use common::IterExt;
    /// let mut combinations = vec![1, 2, 2].into_iter().combinations();
    /// assert_eq!(combinations.next(), Some([1, 2])); // Note: these are the same
    /// assert_eq!(combinations.next(), Some([1, 2])); // Note: these are the same
    /// assert_eq!(combinations.next(), Some([2, 2]));
    /// assert_eq!(combinations.next(), None);
    /// ```
    fn combinations<const K: usize>(self) -> Combinations<Self, K> {
        Combinations::new(self)
    }

    /// Return an iterator adaptor that iterates over the k-length combinations
    /// of the elements from an iterator.
    ///
    /// The iterator produces a new array per iteration, and clones the iterator
    /// elements. If `K` is greater than the length of the input iterator the
    /// resulting iterator adaptor will yield no items.
    ///
    /// # Examples
    ///
    /// ```
    /// use common::IterExt;
    ///
    /// let mut combinations = (1..5).combos();
    /// assert_eq!(combinations.next(), Some([1, 2, 3]));
    /// assert_eq!(combinations.next(), Some([1, 2, 4]));
    /// assert_eq!(combinations.next(), Some([1, 3, 4]));
    /// assert_eq!(combinations.next(), Some([2, 3, 4]));
    /// assert_eq!(combinations.next(), None);
    /// ```
    ///
    /// Note: Combinations does not take into account the equality of the
    /// iterated values.
    ///
    /// ```
    /// # use common::IterExt;
    /// let mut combinations = vec![1, 2, 2].into_iter().combos();
    /// assert_eq!(combinations.next(), Some([1, 2])); // Note: these are the same
    /// assert_eq!(combinations.next(), Some([1, 2])); // Note: these are the same
    /// assert_eq!(combinations.next(), Some([2, 2]));
    /// assert_eq!(combinations.next(), None);
    /// ```
    fn combos<const K: usize>(self) -> Combinations<Self, K> {
        Combinations::new(self)
    }

    /// Return an iterator adaptor that iterates over the k-length permutations
    /// of the elements from an iterator.
    ///
    /// The iterator produces a new array per iteration, and clones the iterator
    /// elements. If `K` is greater than the length of the input iterator the
    /// resulting iterator adaptor will yield no items.
    ///
    /// # Examples
    ///
    /// ```
    /// # use common::IterExt;
    /// let mut permutations = (0..3).permutations();
    /// assert_eq!(permutations.next(), Some([0, 1]));
    /// assert_eq!(permutations.next(), Some([1, 0]));
    /// assert_eq!(permutations.next(), Some([0, 2]));
    /// assert_eq!(permutations.next(), Some([2, 0]));
    /// assert_eq!(permutations.next(), Some([1, 2]));
    /// assert_eq!(permutations.next(), Some([2, 1]));
    /// assert_eq!(permutations.next(), None);
    /// ```
    ///
    /// Note: Permutations does not take into account the equality of the
    /// iterated values.
    ///
    /// ```
    /// # use common::IterExt;
    /// let mut permutations = vec![2, 2].into_iter().permutations();
    /// assert_eq!(permutations.next(), Some([2, 2])); // Note: these are the same
    /// assert_eq!(permutations.next(), Some([2, 2])); // Note: these are the same
    /// assert_eq!(permutations.next(), None);
    /// ```
    fn permutations<const K: usize>(self) -> Permutations<Self, K> {
        Permutations::new(self)
    }

    /// Return an iterator adaptor that iterates over the k-length permutations
    /// of the elements from an iterator.
    ///
    /// The iterator produces a new array per iteration, and clones the iterator
    /// elements. If `K` is greater than the length of the input iterator the
    /// resulting iterator adaptor will yield no items.
    ///
    /// # Examples
    ///
    /// ```
    /// # use common::IterExt;
    /// let mut permutations = (0..3).permuts();
    /// assert_eq!(permutations.next(), Some([0, 1]));
    /// assert_eq!(permutations.next(), Some([1, 0]));
    /// assert_eq!(permutations.next(), Some([0, 2]));
    /// assert_eq!(permutations.next(), Some([2, 0]));
    /// assert_eq!(permutations.next(), Some([1, 2]));
    /// assert_eq!(permutations.next(), Some([2, 1]));
    /// assert_eq!(permutations.next(), None);
    /// ```
    ///
    /// Note: Permutations does not take into account the equality of the
    /// iterated values.
    ///
    /// ```
    /// # use common::IterExt;
    /// let mut permutations = vec![2, 2].into_iter().permuts();
    /// assert_eq!(permutations.next(), Some([2, 2])); // Note: these are the same
    /// assert_eq!(permutations.next(), Some([2, 2])); // Note: these are the same
    /// assert_eq!(permutations.next(), None);
    /// ```
    fn permuts<const K: usize>(self) -> Permutations<Self, K> {
        Permutations::new(self)
    }
}

impl<I> IterExt for I
where
    I: Iterator,
    I::Item: Clone,
{
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn combintation_order() {
        let mut combinations = (1..6).combinations();
        assert_eq!(combinations.next(), Some([1, 2, 3]));
        assert_eq!(combinations.next(), Some([1, 2, 4]));
        assert_eq!(combinations.next(), Some([1, 3, 4]));
        assert_eq!(combinations.next(), Some([2, 3, 4]));
        assert_eq!(combinations.next(), Some([1, 2, 5]));
        assert_eq!(combinations.next(), Some([1, 3, 5]));
        assert_eq!(combinations.next(), Some([2, 3, 5]));
        assert_eq!(combinations.next(), Some([1, 4, 5]));
        assert_eq!(combinations.next(), Some([2, 4, 5]));
        assert_eq!(combinations.next(), Some([3, 4, 5]));
        assert_eq!(combinations.next(), None);
        assert_eq!(combinations.next(), None);
    }

    #[test]
    fn combination_none_on_size_too_big() {
        let mut combinations = (1..2).combinations::<2>();
        assert_eq!(combinations.next(), None);
        assert_eq!(combinations.next(), None);
    }

    #[test]
    fn combination_empty_arr_on_n_zero() {
        let mut combinations = (1..5).combinations();
        assert_eq!(combinations.next(), Some([]));
        assert_eq!(combinations.next(), None);
        assert_eq!(combinations.next(), None);
    }

    #[test]
    fn combination_resume_after_none() {
        let (sender, receiver) = std::sync::mpsc::channel();
        let mut combinations = receiver.try_iter().combinations();
        assert_eq!(combinations.next(), None);

        sender.send(1).unwrap();
        assert_eq!(combinations.next(), None);

        sender.send(2).unwrap();
        assert_eq!(combinations.next(), None);

        sender.send(3).unwrap();
        assert_eq!(combinations.next(), Some([1, 2, 3]));
        assert_eq!(combinations.next(), None);

        sender.send(4).unwrap();
        assert_eq!(combinations.next(), Some([1, 2, 4]));
        assert_eq!(combinations.next(), Some([1, 3, 4]));
        assert_eq!(combinations.next(), Some([2, 3, 4]));
        assert_eq!(combinations.next(), None);
        assert_eq!(combinations.next(), None);
    }

    #[test]
    fn permutation_order() {
        let mut permutations = (1..4).permutations();
        assert_eq!(permutations.next(), Some([1, 2]));
        assert_eq!(permutations.next(), Some([2, 1]));
        assert_eq!(permutations.next(), Some([1, 3]));
        assert_eq!(permutations.next(), Some([3, 1]));
        assert_eq!(permutations.next(), Some([2, 3]));
        assert_eq!(permutations.next(), Some([3, 2]));
        assert_eq!(permutations.next(), None);
        assert_eq!(permutations.next(), None);
    }

    #[test]
    fn full_permutation_full_order() {
        let mut permutations = FullPermutations::new([1, 2, 3]);
        assert_eq!(permutations.next(), Some([1, 2, 3]));
        assert_eq!(permutations.next(), Some([2, 1, 3]));
        assert_eq!(permutations.next(), Some([3, 1, 2]));
        assert_eq!(permutations.next(), Some([1, 3, 2]));
        assert_eq!(permutations.next(), Some([2, 3, 1]));
        assert_eq!(permutations.next(), Some([3, 2, 1]));
        assert_eq!(permutations.next(), None);
        assert_eq!(permutations.next(), None);
    }

    #[test]
    fn permutation_none_on_size_too_big() {
        let mut permutations = (1..2).permutations::<2>();
        assert_eq!(permutations.next(), None);
        assert_eq!(permutations.next(), None);
    }

    #[test]
    fn permutation_empty_arr_on_n_zero() {
        let mut permutations = (1..5).permutations();
        assert_eq!(permutations.next(), Some([]));
        assert_eq!(permutations.next(), None);
        assert_eq!(permutations.next(), None);
    }

    #[test]
    fn permutation_resume_after_none() {
        let (sender, receiver) = std::sync::mpsc::channel();
        let mut permutations = receiver.try_iter().permutations();
        assert_eq!(permutations.next(), None);

        sender.send(1).unwrap();
        assert_eq!(permutations.next(), None);

        sender.send(2).unwrap();
        assert_eq!(permutations.next(), Some([1, 2]));
        assert_eq!(permutations.next(), Some([2, 1]));
        assert_eq!(permutations.next(), None);

        sender.send(3).unwrap();
        assert_eq!(permutations.next(), Some([1, 3]));
        assert_eq!(permutations.next(), Some([3, 1]));
        assert_eq!(permutations.next(), Some([2, 3]));
        assert_eq!(permutations.next(), Some([3, 2]));
        assert_eq!(permutations.next(), None);
        assert_eq!(permutations.next(), None);
    }
}
