//! A fast bump allocation arena.

use anyhow::{Context, Result};
use std::{
    alloc::{alloc, dealloc, Layout},
    cell::Cell,
    iter,
    marker::PhantomData,
    mem,
    ptr::{self, NonNull},
    slice, str,
};

/// An arena to bump allocate into.
///
/// ## No `Drop`s
///
/// Objects that are bump-allocated will never have their `Drop` implementation
/// called &mdash; unless you do it manually yourself. This makes it relatively
/// easy to leak memory or other resources.
///
/// If you have a type which internally manages
///
/// * an allocation from the global heap (e.g. `Vec<T>`),
/// * open file descriptors (e.g. `std::fs::File`), or
/// * any other resource that must be cleaned up (e.g. an `mmap`)
///
/// and relies on its `Drop` implementation to clean up the internal resource,
/// then if you allocate that type with a `Bump`, you need to find a new way to
/// clean up after it yourself.
#[derive(Debug)]
pub struct Bump {
    // The current chunk we are bump allocating within.
    current_chunk_footer: Cell<NonNull<ChunkFooter>>,
}

#[repr(C)]
#[derive(Debug)]
struct ChunkFooter {
    // Pointer to the start of this chunk allocation. This footer is always at
    // the end of the chunk.
    data: NonNull<u8>,
    // The layout of this chunk's allocation.
    layout: Layout,
    // Link to the previous chunk, if any.
    prev: Cell<Option<NonNull<ChunkFooter>>>,
    // Bump allocation finger that is always in the range `self.data..=self`.
    ptr: Cell<NonNull<u8>>,
}

impl Default for Bump {
    fn default() -> Self {
        Bump::new()
    }
}

impl Drop for Bump {
    fn drop(&mut self) {
        unsafe {
            dealloc_chunk_list(Some(self.current_chunk_footer.get()));
        }
    }
}

#[inline]
unsafe fn dealloc_chunk_list(mut footer: Option<NonNull<ChunkFooter>>) {
    while let Some(f) = footer {
        footer = f.as_ref().prev.get();
        dealloc(f.as_ref().data.as_ptr(), f.as_ref().layout);
    }
}

// `Bump`s are safe to send between threads because nothing aliases its owned
// chunks until you start allocating from it. But by the time you allocate from
// it, the returned references to allocations borrow the `Bump` and therefore
// prevent sending the `Bump` across threads until the borrows end.
unsafe impl Send for Bump {}

#[inline]
pub(crate) fn round_up_to(n: usize, divisor: usize) -> Option<usize> {
    debug_assert!(divisor > 0);
    debug_assert!(divisor.is_power_of_two());
    Some(n.checked_add(divisor - 1)? & !(divisor - 1))
}

// After this point, we try to hit page boundaries instead of powers of 2
const PAGE_STRATEGY_CUTOFF: usize = 0x1000;

// We only support alignments of up to 16 bytes for iter_allocated_chunks.
const SUPPORTED_ITER_ALIGNMENT: usize = 16;
const CHUNK_ALIGN: usize = SUPPORTED_ITER_ALIGNMENT;
const FOOTER_SIZE: usize = mem::size_of::<ChunkFooter>();

// Assert that ChunkFooter is at most the supported alignment. This will give a
// compile time error if it is not the case
const _FOOTER_ALIGN_ASSERTION: bool =
    mem::align_of::<ChunkFooter>() <= CHUNK_ALIGN;
const _: [(); _FOOTER_ALIGN_ASSERTION as usize] = [()];

// Maximum typical overhead per allocation imposed by allocators.
const MALLOC_OVERHEAD: usize = 16;

// This is the overhead from malloc, footer and alignment. For instance, if
// we want to request a chunk of memory that has at least X bytes usable for
// allocations (where X is aligned to CHUNK_ALIGN), then we expect that the
// after adding a footer, malloc overhead and alignment, the chunk of memory
// the allocator actually sets asside for us is X+OVERHEAD rounded up to the
// nearest suitable size boundary.
const OVERHEAD: usize =
    (MALLOC_OVERHEAD + FOOTER_SIZE + (CHUNK_ALIGN - 1)) & !(CHUNK_ALIGN - 1);

// Choose a relatively small default initial chunk size, since we double chunk
// sizes as we grow bump arenas to amortize costs of hitting the global
// allocator.
const FIRST_ALLOCATION_GOAL: usize = 1 << 9;

// The actual size of the first allocation is going to be a bit smaller
// than the goal. We need to make room for the footer, and we also need
// take the alignment into account.
const DEFAULT_CHUNK_SIZE_WITHOUT_FOOTER: usize =
    FIRST_ALLOCATION_GOAL - OVERHEAD;

/// Wrapper around `Layout::from_size_align` that adds debug assertions.
#[inline]
unsafe fn layout_from_size_align(size: usize, align: usize) -> Layout {
    if cfg!(debug_assertions) {
        Layout::from_size_align(size, align).unwrap()
    } else {
        Layout::from_size_align_unchecked(size, align)
    }
}

#[inline(never)]
fn allocation_size_overflow<T>() -> T {
    panic!("requested allocation size overflowed")
}

impl Bump {
    /// Construct a new arena to bump allocate into.
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Attempt to construct a new arena to bump allocate into.
    pub fn try_new() -> Result<Bump> {
        Self::try_with_capacity(0)
    }

    /// Construct a new arena with the specified byte capacity to bump allocate
    /// into.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::try_with_capacity(capacity).unwrap_or_else(|_| oom())
    }

    /// Attempt to construct a new arena with the specified byte capacity to
    /// bump allocate into.
    pub fn try_with_capacity(capacity: usize) -> Result<Self> {
        let chunk_footer = Self::new_chunk(
            None,
            Some(unsafe { layout_from_size_align(capacity, 1) }),
            None,
        )
        .with_context(|| "allocation error")?;
        Ok(Self {
            current_chunk_footer: Cell::new(chunk_footer),
        })
    }

    /// Allocate a new chunk and return its initialized footer.
    ///
    /// If given, `layouts` is a tuple of the current chunk size and the
    /// layout of the allocation request that triggered us to fall back to
    /// allocating a new chunk of memory.
    fn new_chunk(
        old_size_with_footer: Option<usize>,
        requested_layout: Option<Layout>,
        prev: Option<NonNull<ChunkFooter>>,
    ) -> Option<NonNull<ChunkFooter>> {
        unsafe {
            // As a sane default, we want our new allocation to be about twice
            // as big as the previous allocation
            let mut new_size_without_footer =
                if let Some(old_size_with_footer) = old_size_with_footer {
                    let old_size_without_footer =
                        old_size_with_footer - FOOTER_SIZE;
                    old_size_without_footer.checked_mul(2)?
                } else {
                    DEFAULT_CHUNK_SIZE_WITHOUT_FOOTER
                };

            let mut align = CHUNK_ALIGN;

            // If we already know we need to fulfill some request,
            // make sure we allocate at least enough to satisfy it
            if let Some(requested_layout) = requested_layout {
                align = align.max(requested_layout.align());
                let requested_size =
                    round_up_to(requested_layout.size(), align)
                        .unwrap_or_else(allocation_size_overflow);
                new_size_without_footer =
                    new_size_without_footer.max(requested_size);
            }

            // We want our allocations to play nice with the memory allocator,
            // and waste as little memory as possible.
            // For small allocations, this means that the entire allocation
            // including the chunk footer and mallocs internal overhead is
            // as close to a power of two as we can go without going over.
            // For larger allocations, we only need to get close to a page
            // boundary without going over.
            if new_size_without_footer < PAGE_STRATEGY_CUTOFF {
                new_size_without_footer = (new_size_without_footer + OVERHEAD)
                    .next_power_of_two()
                    - OVERHEAD;
            } else {
                new_size_without_footer =
                    round_up_to(new_size_without_footer + OVERHEAD, 0x1000)?
                        - OVERHEAD;
            }

            debug_assert_eq!(align % CHUNK_ALIGN, 0);
            debug_assert_eq!(new_size_without_footer % CHUNK_ALIGN, 0);
            let size = new_size_without_footer
                .checked_add(FOOTER_SIZE)
                .unwrap_or_else(allocation_size_overflow);
            let layout = layout_from_size_align(size, align);

            debug_assert!(size >= old_size_with_footer.unwrap_or(0) * 2);

            let data = alloc(layout);
            let data = NonNull::new(data)?;

            // The `ChunkFooter` is at the end of the chunk.
            let footer_ptr = data.as_ptr() as usize + new_size_without_footer;
            debug_assert_eq!((data.as_ptr() as usize) % align, 0);
            debug_assert_eq!(footer_ptr % CHUNK_ALIGN, 0);
            let footer_ptr = footer_ptr as *mut ChunkFooter;

            // The bump pointer is initialized to the end of the range we will
            // bump out of.
            let ptr = Cell::new(NonNull::new_unchecked(footer_ptr as *mut u8));

            ptr::write(
                footer_ptr,
                ChunkFooter {
                    data,
                    layout,
                    prev: Cell::new(prev),
                    ptr,
                },
            );

            Some(NonNull::new_unchecked(footer_ptr))
        }
    }

    pub fn reset(&mut self) {
        unsafe {
            let cur_chunk = self.current_chunk_footer.get();
            let prev_chunk = cur_chunk.as_ref().prev.replace(None);
            dealloc_chunk_list(prev_chunk);
            cur_chunk.as_ref().ptr.set(cur_chunk.cast());

            debug_assert!(
                self.current_chunk_footer
                    .get()
                    .as_ref()
                    .prev
                    .get()
                    .is_none(),
                "We should only have a single chunk"
            );
            debug_assert_eq!(
                self.current_chunk_footer.get().as_ref().ptr.get(),
                self.current_chunk_footer.get().cast(),
                "Our chunl's bump finger should be reset to the start of its allocation"
            );
        }
    }

    /// Allocate an object in this `Bump` and return an exclusive reference to
    /// it.
    ///
    /// ## Panics
    ///
    /// Panics if reserving space for `T` would cause an overflow.
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub fn alloc<T>(&self, val: T) -> &mut T {
        self.alloc_with(|| val)
    }

    /// Pre-allocate space for an object in this `Bump`, initializes it using
    /// the closure, then returns an exclusive reference to it.
    ///
    /// Calling `bump.alloc(x)` is essentially equivalent to calling
    /// `bump.alloc_with(|| x)`. However if you use `alloc_with`, then the
    /// closure will not be invoked until after allocating space for storing
    /// `x` on the heap.
    ///
    /// This can be useful in certain edge-cases related to compiler
    /// optimizations. When evaluating `bump.alloc(x)`, semantically `x` is
    /// first put on the stack and then moved onto the heap. In some cases,
    /// the compiler is able to optimize this into constructing `x` directly
    /// on the heap, however in many cases it does not.
    ///
    /// The function `alloc_with` tries to help the compiler be smarter. In
    /// most cases doing `bump.alloc_with(|| x)` on release mode will be
    /// enough to help the compiler to realize this optimization is valid
    /// and construct `x` directly onto the heap.
    ///
    /// ## Warning
    ///
    /// This function critically depends on compiler optimizations to achieve
    /// its desired effect. This means that it is not an effective tool when
    /// compiling without optimizations on.
    ///
    /// Even when optimizations are on, this function does not **guarantee**
    /// that the value is constructed on the heap. To the best of our
    /// knowledge no such guarantee can be made in stable Rust as of 1.33.
    ///
    /// ## Panics
    ///
    /// Panics if reserving space for `T` would cause an overflow.
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub fn alloc_with<F, T>(&self, f: F) -> &mut T
    where
        F: FnOnce() -> T,
    {
        #[inline(always)]
        unsafe fn inner_writer<T, F>(ptr: *mut T, f: F)
        where
            F: FnOnce() -> T,
        {
            // This function is translated as:
            // - allocate space for a T on the stack
            // - call f() with the return value being put onto this stack space
            // - memcpy from the stack to the heap
            //
            // Ideally we want LLVM to always realize that doing a stack
            // allocation is unnecessary and optimize the code so it writes
            // directly into the heap instead. It seems we get it to realize
            // this most consistently if we put this critical line into it's
            // own function instead of inlining it into the surrounding code.
            ptr::write(ptr, f())
        }

        let layout = Layout::new::<T>();

        unsafe {
            let p = self.alloc_layout(layout);
            let p = p.as_ptr() as *mut T;
            inner_writer(p, f);
            &mut *p
        }
    }

    /// `Copy` a slice into this `Bump` and return an exclusive reference to
    /// the copy.
    ///
    /// ## Panics
    ///
    /// Panics if reserving space for the slice would cause an overflow.
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub fn alloc_slice_copy<T>(&self, src: &[T]) -> &mut [T]
    where
        T: Copy,
    {
        let layout = Layout::for_value(src);
        let dst = self.alloc_layout(layout).cast::<T>();

        unsafe {
            ptr::copy_nonoverlapping(src.as_ptr(), dst.as_ptr(), src.len());
            slice::from_raw_parts_mut(dst.as_ptr(), src.len())
        }
    }

    /// `Clone` a slice into this `Bump` and return an exclusive reference to
    /// the clone. Prefer `alloc_slice_copy` if `T` is `Copy`.
    ///
    /// ## Panics
    ///
    /// Panics if reserving space for the slice would cause an overflow.
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub fn alloc_slice_clone<T>(&self, src: &[T]) -> &mut [T]
    where
        T: Clone,
    {
        let layout = Layout::for_value(src);
        let dst = self.alloc_layout(layout).cast::<T>();

        unsafe {
            for (i, val) in src.iter().cloned().enumerate() {
                ptr::write(dst.as_ptr().add(i), val);
            }

            slice::from_raw_parts_mut(dst.as_ptr(), src.len())
        }
    }

    /// `Copy` a string slice into this `Bump` and return an exclusive reference
    /// to it.
    ///
    /// ## Panics
    ///
    /// Panics if reserving space for the string would cause an overflow.
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub fn alloc_str(&self, src: &str) -> &mut str {
        let buffer = self.alloc_slice_copy(src.as_bytes());
        // SAFETY: This is OK, because it already came in as str,
        // so it is guaranteed to be utf8
        unsafe { str::from_utf8_unchecked_mut(buffer) }
    }

    /// Allocates a new slice of size `len` into this `Bump` and returns an
    /// exclusive reference to the copy.
    ///
    /// The elements of the slice are initialized using the supplied closure.
    /// The closure argument is the position in the slice.
    ///
    /// ## Panics
    ///
    /// Panics if reserving space for the slice would cause an overflow.
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub fn alloc_slice_fill_with<T, F>(&self, len: usize, mut f: F) -> &mut [T]
    where
        F: FnMut(usize) -> T,
    {
        let layout = Layout::array::<T>(len).unwrap_or_else(|_| oom());
        let dst = self.alloc_layout(layout).cast::<T>();

        unsafe {
            for i in 0..len {
                ptr::write(dst.as_ptr().add(i), f(i));
            }

            let result = slice::from_raw_parts_mut(dst.as_ptr(), len);
            debug_assert_eq!(Layout::for_value(result), layout);
            result
        }
    }

    /// Allocates a new slice of size `len` into this `Bump` and returns an
    /// exclusive reference to the copy.
    ///
    /// All elements of the slice are initialized to `value`.
    ///
    /// ## Panics
    ///
    /// Panics if reserving space for the slice would cause an overflow.
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub fn alloc_slice_fill_copy<T: Copy>(
        &self,
        len: usize,
        value: T,
    ) -> &mut [T] {
        self.alloc_slice_fill_with(len, |_| value)
    }

    /// Allocates a new slice of size `len` slice into this `Bump` and return an
    /// exclusive reference to the copy.
    ///
    /// All elements of the slice are initialized to `value.clone()`.
    ///
    /// ## Panics
    ///
    /// Panics if reserving space for the slice would cause an overflow.
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub fn alloc_slice_fill_clone<T: Clone>(
        &self,
        len: usize,
        value: &T,
    ) -> &mut [T] {
        self.alloc_slice_fill_with(len, |_| value.clone())
    }

    /// Allocates a new slice of size `len` slice into this `Bump` and return an
    /// exclusive reference to the copy.
    ///
    /// The elements are initialized using the supplied iterator.
    ///
    /// ## Panics
    ///
    /// Panics if reserving space for the slice would cause an overflow, or if
    /// the supplied iterator returns fewer elements than it promised.
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub fn alloc_slice_fill_iter<T, I>(&self, iter: I) -> &mut [T]
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut iter = iter.into_iter();
        self.alloc_slice_fill_with(iter.len(), |_| {
            iter.next().expect("Iterator supplied too few elements")
        })
    }

    /// Allocates a new slice of size `len` slice into this `Bump` and return an
    /// exclusive reference to the copy.
    ///
    /// All elements of the slice are initialized to `T::default()`.
    ///
    /// ## Panics
    ///
    /// Panics if reserving space for the slice would cause an overflow.
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub fn alloc_slice_fill_default<T: Default>(&self, len: usize) -> &mut [T] {
        self.alloc_slice_fill_with(len, |_| T::default())
    }

    /// Allocate space for an object with the given `Layout`.
    ///
    /// The returned pointer points at uninitialized memory, and should be
    /// initialized with
    /// [`std::ptr::write`](https://doc.rust-lang.org/std/ptr/fn.write.html).
    #[inline(always)]
    pub fn alloc_layout(&self, layout: Layout) -> NonNull<u8> {
        self.try_alloc_layout(layout).unwrap_or_else(|_| oom())
    }

    /// Attempts to allocate space for an object with the given `Layout` or else
    /// returns an `Err`.
    ///
    /// The returned pointer points at uninitialized memory, and should be
    /// initialized with
    /// [`std::ptr::write`](https://doc.rust-lang.org/std/ptr/fn.write.html).
    #[inline(always)]
    pub fn try_alloc_layout(&self, layout: Layout) -> Result<NonNull<u8>> {
        if let Some(p) = self.try_alloc_layout_fast(layout) {
            Ok(p)
        } else {
            self.alloc_layout_slow(layout)
                .with_context(|| "error alloc_layout_slow")
        }
    }

    #[inline(always)]
    fn try_alloc_layout_fast(&self, layout: Layout) -> Option<NonNull<u8>> {
        unsafe {
            // We don't need to check for ZSTs here since they will
            // automatically be handled properly: the pointer will
            // be bumped by zero bytes, modulo alignment. This keeps
            // the fast path optimized for non-ZSTs, which are much
            // more common.
            let footer = self.current_chunk_footer.get();
            let footer = footer.as_ref();
            let ptr = footer.ptr.get().as_ptr() as usize;
            let start = footer.data.as_ptr() as usize;
            debug_assert!(start <= ptr);
            debug_assert!(ptr <= footer as *const _ as usize);

            let ptr = ptr.checked_sub(layout.size())?;
            let aligned_ptr = ptr & !(layout.align() - 1);

            if aligned_ptr >= start {
                let aligned_ptr =
                    NonNull::new_unchecked(aligned_ptr as *mut u8);
                footer.ptr.set(aligned_ptr);
                Some(aligned_ptr)
            } else {
                None
            }
        }
    }

    /// Gets the remaining capacity in the current chunk (in bytes).
    pub fn chunk_capacity(&self) -> usize {
        let current_footer = self.current_chunk_footer.get();
        let current_footer = unsafe { current_footer.as_ref() };

        current_footer as *const _ as usize
            - current_footer.data.as_ptr() as usize
    }

    #[inline(never)]
    fn alloc_layout_slow(&self, layout: Layout) -> Option<NonNull<u8>> {
        unsafe {
            let size = layout.size();
            // Get a new chunk from the global allocator.
            let current_footer = self.current_chunk_footer.get();
            let current_layout = current_footer.as_ref().layout;
            let new_footer = Bump::new_chunk(
                Some(current_layout.size()),
                Some(layout),
                Some(current_footer),
            )?;
            debug_assert_eq!(
                new_footer.as_ref().data.as_ptr() as usize % layout.align(),
                0
            );

            // Set the new chunk as our new current chunk.
            self.current_chunk_footer.set(new_footer);
            let new_footer = new_footer.as_ref();

            // Move the bump ptr finger down to allocate room for `val`. We know
            // this can't overflow because we successfully allocated a chunk of
            // at least the requested size.
            let ptr = new_footer.ptr.get().as_ptr() as usize - size;
            // Round the pointer down to the requested alignment.
            let ptr = ptr & !(layout.align() - 1);
            debug_assert!(
                ptr <= new_footer as *const _ as usize,
                "{:#x} <= {:#x}",
                ptr,
                new_footer as *const _ as usize
            );
            let ptr = NonNull::new_unchecked(ptr as *mut u8);
            new_footer.ptr.set(ptr);

            // Return a pointer to the freshly allocated region in this chunk.
            Some(ptr)
        }
    }

    /// Returns an iterator over each chunk of allocated memory that
    /// this arena has bump allocated into.
    ///
    /// The chunks are returned ordered by allocation time, with the most
    /// recently allocated chunk being returned first, and the least recently
    /// allocated chunk being returned last.
    ///
    /// The values inside each chunk are also ordered by allocation time, with
    /// the most recent allocation being earlier in the slice, and the least
    /// recent allocation being towards the end of the slice.
    ///
    /// ## Safety
    ///
    /// Because this method takes `&mut self`, we know that the bump arena
    /// reference is unique and therefore there aren't any active references to
    /// any of the objects we've allocated in it either. This potential aliasing
    /// of exclusive references is one common footgun for unsafe code that we
    /// don't need to worry about here.
    ///
    /// However, there could be regions of uninitialized memory used as padding
    /// between allocations, which is why this iterator has items of type
    /// `[MaybeUninit<u8>]`, instead of simply `[u8]`.
    ///
    /// The only way to guarantee that there is no padding between allocations
    /// or within allocated objects is if all of these properties hold:
    ///
    /// 1. Every object allocated in this arena has the same alignment,
    ///    and that alignment is at most 16.
    /// 2. Every object's size is a multiple of its alignment.
    /// 3. None of the objects allocated in this arena contain any internal
    ///    padding.
    ///
    /// If you want to use this `iter_allocated_chunks` method, it is *your*
    /// responsibility to ensure that these properties hold before calling
    /// `MaybeUninit::assume_init` or otherwise reading the returned values.
    ///
    /// Finally, you must also ensure that any values allocated into the bump
    /// arena have not had their `Drop` implementations called on them,
    /// e.g. after dropping a [`bumpalo::boxed::Box<T>`][crate::boxed::Box].
    pub fn iter_allocated_chunks(&mut self) -> ChunkIter<'_> {
        ChunkIter {
            footer: Some(self.current_chunk_footer.get()),
            bump: PhantomData,
        }
    }

    /// Calculates the number of bytes currently allocated across all chunks.
    ///
    /// If you allocate types of different alignments or types with
    /// larger-than-typical alignment in the same arena, some padding
    /// bytes might get allocated in the bump arena. Note that those padding
    /// bytes will add to this method's resulting sum, so you cannot rely
    /// on it only counting the sum of the sizes of the things
    /// you've allocated in the arena.
    pub fn allocated_bytes(&self) -> usize {
        let mut footer = Some(self.current_chunk_footer.get());
        let mut bytes = 0;

        while let Some(f) = footer {
            let foot = unsafe { f.as_ref() };
            let ptr = foot.ptr.get().as_ptr() as usize;
            debug_assert!(ptr <= foot as *const _ as usize);

            bytes += foot as *const _ as usize - ptr;
            footer = foot.prev.get();
        }

        bytes
    }

    #[inline]
    unsafe fn is_last_allocation(&self, ptr: NonNull<u8>) -> bool {
        let footer = self.current_chunk_footer.get();
        let footer = footer.as_ref();
        footer.ptr.get() == ptr
    }
}

/// An iterator over each chunk of allocated memory that
/// an arena has bump allocated into.
///
/// The chunks are returned ordered by allocation time, with the most recently
/// allocated chunk being returned first.
///
/// The values inside each chunk is also ordered by allocation time, with the
/// most recent allocation being earlier in the slice.
///
/// This struct is created by the [`iter_allocated_chunks`] method on
/// [`Bump`]. See that function for a safety description regarding reading from
/// the returned items.
#[derive(Debug)]
pub struct ChunkIter<'a> {
    footer: Option<NonNull<ChunkFooter>>,
    bump: PhantomData<&'a mut Bump>,
}

impl<'a> Iterator for ChunkIter<'a> {
    type Item = &'a [mem::MaybeUninit<u8>];

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let foot = self.footer?;
            let foot = foot.as_ref();
            let data = foot.data.as_ptr() as usize;
            let ptr = foot.ptr.get().as_ptr() as usize;
            debug_assert!(data <= ptr);
            debug_assert!(ptr <= foot as *const _ as usize);

            let len = foot as *const _ as usize - ptr;
            let slice =
                slice::from_raw_parts(ptr as *const mem::MaybeUninit<u8>, len);
            self.footer = foot.prev.get();
            Some(slice)
        }
    }
}

impl<'a> iter::FusedIterator for ChunkIter<'a> {}

#[inline(never)]
#[cold]
fn oom() -> ! {
    panic!("out of memory")
}

pub mod alloc {
    //! Memory allocation APIS
    #![allow(unstable_name_collisions, dead_code)]

    use anyhow::{Context, Result};
    pub use std::alloc::{Layout, LayoutErr};
    use std::{
        cmp, fmt, mem,
        ptr::{self, NonNull},
        usize,
    };

    fn new_layout_err() -> LayoutErr {
        Layout::from_size_align(1, 3).unwrap_err()
    }

    pub fn handle_alloc_error(layout: Layout) -> ! {
        panic!("encountered allocation error: {:?}", layout)
    }

    pub trait UnstableLayoutMethods {
        fn padding_needed_for(&self, align: usize) -> usize;
        fn repeat(&self, n: usize) -> Result<(Layout, usize)>;
        fn array<T>(n: usize) -> Result<Layout>;
    }

    impl UnstableLayoutMethods for Layout {
        fn padding_needed_for(&self, align: usize) -> usize {
            let len = self.size();

            // Rounded up value is:
            //   len_rounded_up = (len + align - 1) & !(align - 1);
            // and then we return the padding difference: `len_rounded_up -
            // len`.
            //
            // We use modular arithmetic throughout:
            //
            // 1. align is guaranteed to be > 0, so align - 1 is always
            //    valid.
            //
            // 2. `len + align - 1` can overflow by at most `align - 1`,
            //    so the &-mask wth `!(align - 1)` will ensure that in the
            //    case of overflow, `len_rounded_up` will itself be 0.
            //    Thus the returned padding, when added to `len`, yields 0,
            //    which trivially satisfies the alignment `align`.
            //
            // (Of course, attempts to allocate blocks of memory whose
            // size and padding overflow in the above manner should cause
            // the allocator to yield an error anyway.)

            let len_rounded_up = len.wrapping_add(align).wrapping_sub(1)
                & !align.wrapping_sub(1);
            len_rounded_up.wrapping_sub(len)
        }

        fn repeat(&self, n: usize) -> Result<(Layout, usize)> {
            let padded_size = self
                .size()
                .checked_add(self.padding_needed_for(self.align()))
                .with_context(|| "error padding layout")?;
            let alloc_size = padded_size
                .checked_mul(n)
                .with_context(|| "error multiply padded layout")?;

            // SAFETY: self.align is already known to be valid and alloc_size
            // has been padded already.
            unsafe {
                Ok((
                    Layout::from_size_align_unchecked(alloc_size, self.align()),
                    padded_size,
                ))
            }
        }

        fn array<T>(n: usize) -> Result<Layout> {
            Layout::new::<T>().repeat(n).map(|(k, offs)| {
                debug_assert!(offs == mem::size_of::<T>());
                k
            })
        }
    }

    /// Represents the combination of a starting address and
    /// a total capacity of the returned block.
    #[derive(Debug)]
    pub struct Excess(pub NonNull<u8>, pub usize);

    fn size_align<T>() -> (usize, usize) {
        (mem::size_of::<T>(), mem::align_of::<T>())
    }

    /// The `AllocErr` error indicates an allocation failure
    /// that may be due to resource exhaustion or to
    /// something wrong when combining the given input arguments with this
    /// allocator.
    #[derive(Debug, Clone, Eq, PartialEq)]
    pub struct AllocErr;

    impl fmt::Display for AllocErr {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("memory allocation failed")
        }
    }

    #[derive(Debug, Clone, Eq, PartialEq)]
    pub struct CannotReallocInPlace;

    impl CannotReallocInPlace {
        pub fn description(&self) -> &str {
            "cannot reallocate allocator's memory in place"
        }
    }

    impl fmt::Display for CannotReallocInPlace {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.description())
        }
    }

    /// An implementation of `Alloc` can allocate, reallocate, and
    /// deallocate arbitrary blocks of data described via `Layout`.
    ///
    /// Some of the methods require that a memory block be *currently
    /// allocated* via an allocator. This means that:
    ///
    /// * the starting address for that memory block was previously returned by
    ///   a previous call to an allocation method (`alloc`, `alloc_zeroed`,
    ///   `alloc_excess`, `alloc_one`, `alloc_array`) or reallocation method
    ///   (`realloc`, `realloc_excess`, or `realloc_array`), and
    ///
    /// * the memory block has not been subsequently deallocated, where blocks
    ///   are deallocated either by being passed to a deallocation method
    ///   (`dealloc`, `dealloc_one`, `dealloc_array`) or by being passed to a
    ///   reallocation method (see above) that returns `Ok`.
    ///
    /// A note regarding zero-sized types and zero-sized layouts: many
    /// methods in the `Alloc` trait state that allocation requests
    /// must be non-zero size, or else undefined behavior can result.
    ///
    /// * However, some higher-level allocation methods (`alloc_one`,
    ///   `alloc_array`) are well-defined on zero-sized types and can optionally
    ///   support them: it is left up to the implementor whether to return
    ///   `Err`, or to return `Ok` with some pointer.
    ///
    /// * If an `Alloc` implementation chooses to return `Ok` in this case (i.e.
    ///   the pointer denotes a zero-sized inaccessible block) then that
    ///   returned pointer must be considered "currently allocated". On such an
    ///   allocator, *all* methods that take currently-allocated pointers as
    ///   inputs must accept these zero-sized pointers, *without* causing
    ///   undefined behavior.
    ///
    /// * In other words, if a zero-sized pointer can flow out of an allocator,
    ///   then that allocator must likewise accept that pointer flowing back
    ///   into its deallocation and reallocation methods.
    ///
    /// Some of the methods require that a layout *fit* a memory block.
    /// What it means for a layout to "fit" a memory block means (or
    /// equivalently, for a memory block to "fit" a layout) is that the
    /// following two conditions must hold:
    ///
    /// 1. The block's starting address must be aligned to `layout.align()`.
    ///
    /// 2. The block's size must fall in the range `[use_min, use_max]`, where:
    ///
    ///    * `use_min` is `self.usable_size(layout).0`, and
    ///
    ///    * `use_max` is the capacity that was (or would have been) returned
    ///      when (if) the block was allocated via a call to `alloc_excess` or
    ///      `realloc_excess`.
    ///
    /// Note that:
    ///
    ///  * the size of the layout most recently used to allocate the block is
    ///    guaranteed to be in the range `[use_min, use_max]`, and
    ///
    ///  * a lower-bound on `use_max` can be safely approximated by a call to
    ///    `usable_size`.
    ///
    ///  * if a layout `k` fits a memory block (denoted by `ptr`) currently
    ///    allocated via an allocator `a`, then it is legal to use that layout
    ///    to deallocate it, i.e. `a.dealloc(ptr, k);`.
    ///
    /// # Unsafety
    ///
    /// The `Alloc` trait is an `unsafe` trait for a number of reasons, and
    /// implementors must ensure that they adhere to these contracts:
    ///
    /// * Pointers returned from allocation functions must point to valid memory
    ///   and retain their validity until at least the instance of `Alloc` is
    ///   dropped itself.
    ///
    /// * `Layout` queries and calculations in general must be correct. Callers
    ///   of this trait are allowed to rely on the contracts defined on each
    ///   method, and implementors must ensure such contracts remain true.
    pub unsafe trait Alloc {
        /// Returns a pointer meeting the size and alignment guarantees of
        /// `layout`.
        ///
        /// If this method returns an `Ok(addr)`, then the `addr` returned
        /// will be non-null address pointing to a block of storage
        /// suitable for holding an instance of `layout`.
        ///
        /// The returned block of storage may or may not have its contents
        /// initialized. (Extension subtraits might restrict this
        /// behavior, e.g. to ensure initialization to particular sets of
        /// bit patterns.)
        ///
        /// # Safety
        ///
        /// This function is unsafe because undefined behavior can result
        /// if the caller does not ensure that `layout` has non-zero size.
        ///
        /// (Extension subtraits might provide more specific bounds on
        /// behavior, e.g. guarantee a sentinel address or a null pointer
        /// in response to a zero-size allocation request.)
        unsafe fn alloc(&mut self, layout: Layout) -> Result<NonNull<u8>>;

        /// Deallocate the memory referenced by `ptr`.
        ///
        /// # Safety
        ///
        /// This function is unsafe because undefined behavior can result
        /// if the caller does not ensure all of the following:
        ///
        /// * `ptr` must denote a block of memory currently allocated via this
        ///   allocator,
        ///
        /// * `layout` must *fit* that block of memory,
        ///
        /// * In addition to fitting the block of memory `layout`, the alignment
        ///   of the `layout` must match the alignment used to allocate that
        ///   block of memory.
        unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: Layout);

        /// Returns bounds on the guaranteed usable size of a successful
        /// allocation created with the specified `layout`.
        ///
        /// In particular, if one has a memory block allocated via a given
        /// allocator `a` and layout `k` where `a.usable_size(k)` returns
        /// `(l, u)`, then one can pass that block to `a.dealloc()` with a
        /// layout in the size range [l, u].
        ///
        /// (All implementors of `usable_size` must ensure that
        /// `l <= k.size() <= u`)
        ///
        /// Both the lower- and upper-bounds (`l` and `u` respectively)
        /// are provided, because an allocator based on size classes could
        /// misbehave if one attempts to deallocate a block without
        /// providing a correct value for its size (i.e., one within the
        /// range `[l, u]`).
        ///
        /// Clients who wish to make use of excess capacity are encouraged
        /// to use the `alloc_excess` and `realloc_excess` instead, as
        /// this method is constrained to report conservative values that
        /// serve as valid bounds for *all possible* allocation method
        /// calls.
        ///
        /// However, for clients that do not wish to track the capacity
        /// returned by `alloc_excess` locally, this method is likely to
        /// produce useful results.
        #[inline]
        fn usable_size(&self, layout: &Layout) -> (usize, usize) {
            (layout.size(), layout.size())
        }

        /// Returns a pointer suitable for holding data described by
        /// a new layout with `layout`’s alignment and a size given
        /// by `new_size`. To
        /// accomplish this, this may extend or shrink the allocation
        /// referenced by `ptr` to fit the new layout.
        ///
        /// If this returns `Ok`, then ownership of the memory block
        /// referenced by `ptr` has been transferred to this
        /// allocator. The memory may or may not have been freed, and
        /// should be considered unusable (unless of course it was
        /// transferred back to the caller again via the return value of
        /// this method).
        ///
        /// If this method returns `Err`, then ownership of the memory
        /// block has not been transferred to this allocator, and the
        /// contents of the memory block are unaltered.
        ///
        /// # Safety
        ///
        /// This function is unsafe because undefined behavior can result
        /// if the caller does not ensure all of the following:
        ///
        /// * `ptr` must be currently allocated via this allocator,
        ///
        /// * `layout` must *fit* the `ptr` (see above). (The `new_size`
        ///   argument need not fit it.)
        ///
        /// * `new_size` must be greater than zero.
        ///
        /// * `new_size`, when rounded up to the nearest multiple of
        ///   `layout.align()`, must not overflow (i.e. the rounded value must
        ///   be less than `usize::MAX`).
        ///
        /// (Extension subtraits might provide more specific bounds on
        /// behavior, e.g. guarantee a sentinel address or a null pointer
        /// in response to a zero-size allocation request.)
        unsafe fn realloc(
            &mut self,
            ptr: NonNull<u8>,
            layout: Layout,
            new_size: usize,
        ) -> Result<NonNull<u8>> {
            let old_size = layout.size();

            if new_size >= old_size {
                if let Ok(()) = self.grow_in_place(ptr, layout, new_size) {
                    return Ok(ptr);
                }
            } else if new_size < old_size {
                if let Ok(()) = self.shrink_in_place(ptr, layout, new_size) {
                    return Ok(ptr);
                }
            }

            // otherwise, fall back on alloc + copy + dealloc.
            let new_layout =
                Layout::from_size_align_unchecked(new_size, layout.align());
            let result = self.alloc(new_layout);
            if let Ok(new_ptr) = result {
                ptr::copy_nonoverlapping(
                    ptr.as_ptr(),
                    new_ptr.as_ptr(),
                    cmp::min(old_size, new_size),
                );
                self.dealloc(ptr, layout);
            }
            result
        }

        /// Behaves like `alloc`, but also ensures that the contents
        /// are set to zero before being returned.
        ///
        /// # Safety
        ///
        /// This function is unsafe for the same reasons that `alloc` is.
        unsafe fn alloc_zeroed(
            &mut self,
            layout: Layout,
        ) -> Result<NonNull<u8>> {
            let size = layout.size();
            let p = self.alloc(layout);
            if let Ok(p) = p {
                ptr::write_bytes(p.as_ptr(), 0, size);
            }
            p
        }

        /// Behaves like `alloc`, but also returns the whole size of
        /// the returned block. For some `layout` inputs, like arrays, this
        /// may include extra storage usable for additional data.
        ///
        /// # Safety
        ///
        /// This function is unsafe for the same reasons that `alloc` is.
        unsafe fn alloc_excess(&mut self, layout: Layout) -> Result<Excess> {
            let usable_size = self.usable_size(&layout);
            self.alloc(layout).map(|p| Excess(p, usable_size.1))
        }

        /// Behaves like `realloc`, but also returns the whole size of
        /// the returned block. For some `layout` inputs, like arrays, this
        /// may include extra storage usable for additional data.
        ///
        /// # Safety
        ///
        /// This function is unsafe for the same reasons that `realloc` is.
        unsafe fn realloc_excess(
            &mut self,
            ptr: NonNull<u8>,
            layout: Layout,
            new_size: usize,
        ) -> Result<Excess> {
            let new_layout =
                Layout::from_size_align_unchecked(new_size, layout.align());
            let usable_size = self.usable_size(&new_layout);
            self.realloc(ptr, layout, new_size)
                .map(|p| Excess(p, usable_size.1))
        }

        /// Attempts to extend the allocation referenced by `ptr` to fit
        /// `new_size`.
        ///
        /// If this returns `Ok`, then the allocator has asserted that the
        /// memory block referenced by `ptr` now fits `new_size`, and thus can
        /// be used to carry data of a layout of that size and same alignment as
        /// `layout`. (The allocator is allowed to
        /// expend effort to accomplish this, such as extending the memory block
        /// to include successor blocks, or virtual memory tricks.)
        ///
        /// Regardless of what this method returns, ownership of the
        /// memory block referenced by `ptr` has not been transferred, and
        /// the contents of the memory block are unaltered.
        ///
        /// # Safety
        ///
        /// This function is unsafe because undefined behavior can result
        /// if the caller does not ensure all of the following:
        ///
        /// * `ptr` must be currently allocated via this allocator,
        ///
        /// * `layout` must *fit* the `ptr` (see above); note the `new_size`
        ///   argument need not fit it,
        ///
        /// * `new_size` must not be less than `layout.size()`,
        unsafe fn grow_in_place(
            &mut self,
            ptr: NonNull<u8>,
            layout: Layout,
            new_size: usize,
        ) -> Result<()> {
            let _ = ptr; // this default implementation doesn't care about the actual
                         // address.
            debug_assert!(new_size >= layout.size());
            let (_l, u) = self.usable_size(&layout);
            if new_size <= u {
                Ok(())
            } else {
                Err(anyhow::anyhow!("cannot realloc in place"))
            }
        }

        /// Attempts to shrink the allocation referenced by `ptr` to fit
        /// `new_size`.
        ///
        /// If this returns `Ok`, then the allocator has asserted that the
        /// memory block referenced by `ptr` now fits `new_size`, and
        /// thus can only be used to carry data of that smaller
        /// layout. (The allocator is allowed to take advantage of this,
        /// carving off portions of the block for reuse elsewhere.) The
        /// truncated contents of the block within the smaller layout are
        /// unaltered, and ownership of block has not been transferred.
        ///
        /// If this returns `Err`, then the memory block is considered to
        /// still represent the original (larger) `layout`. None of the
        /// block has been carved off for reuse elsewhere, ownership of
        /// the memory block has not been transferred, and the contents of
        /// the memory block are unaltered.
        ///
        /// # Safety
        ///
        /// This function is unsafe because undefined behavior can result
        /// if the caller does not ensure all of the following:
        ///
        /// * `ptr` must be currently allocated via this allocator,
        ///
        /// * `layout` must *fit* the `ptr` (see above); note the `new_size`
        ///   argument need not fit it,
        ///
        /// * `new_size` must not be greater than `layout.size()` (and must be
        ///   greater than zero),
        unsafe fn shrink_in_place(
            &mut self,
            ptr: NonNull<u8>,
            layout: Layout,
            new_size: usize,
        ) -> Result<()> {
            let _ = ptr; // this default implementation doesn't care about the actual
                         // address.
            debug_assert!(new_size <= layout.size());
            let (l, _u) = self.usable_size(&layout);
            if l <= new_size {
                Ok(())
            } else {
                Err(anyhow::anyhow!("cannot realloc in place"))
            }
        }

        /// Allocates a block suitable for holding an instance of `T`.
        ///
        /// Captures a common usage pattern for allocators.
        ///
        /// The returned block is suitable for passing to the
        /// `alloc`/`realloc` methods of this allocator.
        ///
        /// Note to implementors: If this returns `Ok(ptr)`, then `ptr`
        /// must be considered "currently allocated" and must be
        /// acceptable input to methods such as `realloc` or `dealloc`,
        /// *even if* `T` is a zero-sized type. In other words, if your
        /// `Alloc` implementation overrides this method in a manner
        /// that can return a zero-sized `ptr`, then all reallocation and
        /// deallocation methods need to be similarly overridden to accept
        /// such values as input.
        fn alloc_one<T>(&mut self) -> Result<NonNull<T>>
        where
            Self: Sized,
        {
            let k = Layout::new::<T>();
            if k.size() > 0 {
                unsafe { self.alloc(k).map(|p| p.cast()) }
            } else {
                Err(anyhow::anyhow!("alloc error"))
            }
        }

        /// Deallocates a block suitable for holding an instance of `T`.
        ///
        /// The given block must have been produced by this allocator,
        /// and must be suitable for storing a `T` (in terms of alignment
        /// as well as minimum and maximum size); otherwise yields
        /// undefined behavior.
        ///
        /// Captures a common usage pattern for allocators.
        ///
        /// # Safety
        ///
        /// This function is unsafe because undefined behavior can result
        /// if the caller does not ensure both:
        ///
        /// * `ptr` must denote a block of memory currently allocated via this
        ///   allocator
        ///
        /// * the layout of `T` must *fit* that block of memory.
        unsafe fn dealloc_one<T>(&mut self, ptr: NonNull<T>)
        where
            Self: Sized,
        {
            let k = Layout::new::<T>();
            if k.size() > 0 {
                self.dealloc(ptr.cast(), k);
            }
        }

        /// Allocates a block suitable for holding `n` instances of `T`.
        ///
        /// Captures a common usage pattern for allocators.
        ///
        /// The returned block is suitable for passing to the
        /// `alloc`/`realloc` methods of this allocator.
        ///
        /// Note to implementors: If this returns `Ok(ptr)`, then `ptr`
        /// must be considered "currently allocated" and must be
        /// acceptable input to methods such as `realloc` or `dealloc`,
        /// *even if* `T` is a zero-sized type. In other words, if your
        /// `Alloc` implementation overrides this method in a manner
        /// that can return a zero-sized `ptr`, then all reallocation and
        /// deallocation methods need to be similarly overridden to accept
        /// such values as input.
        fn alloc_array<T>(&mut self, n: usize) -> Result<NonNull<T>>
        where
            Self: Sized,
        {
            match Layout::array::<T>(n) {
                Ok(layout) if layout.size() > 0 => unsafe {
                    self.alloc(layout).map(|p| p.cast())
                },
                _ => Err(anyhow::anyhow!("alloc error")),
            }
        }

        /// Reallocates a block previously suitable for holding `n_old`
        /// instances of `T`, returning a block suitable for holding
        /// `n_new` instances of `T`.
        ///
        /// Captures a common usage pattern for allocators.
        ///
        /// The returned block is suitable for passing to the
        /// `alloc`/`realloc` methods of this allocator.
        ///
        /// # Safety
        ///
        /// This function is unsafe because undefined behavior can result
        /// if the caller does not ensure all of the following:
        ///
        /// * `ptr` must be currently allocated via this allocator,
        ///
        /// * the layout of `[T; n_old]` must *fit* that block of memory.
        unsafe fn realloc_array<T>(
            &mut self,
            ptr: NonNull<T>,
            n_old: usize,
            n_new: usize,
        ) -> Result<NonNull<T>>
        where
            Self: Sized,
        {
            match (Layout::array::<T>(n_old), Layout::array::<T>(n_new)) {
                (Ok(ref k_old), Ok(ref k_new))
                    if k_old.size() > 0 && k_new.size() > 0 =>
                {
                    debug_assert!(k_old.align() == k_new.align());
                    self.realloc(ptr.cast(), k_old.clone(), k_new.size())
                        .map(NonNull::cast)
                }
                _ => Err(anyhow::anyhow!("alloc error")),
            }
        }

        /// Deallocates a block suitable for holding `n` instances of `T`.
        ///
        /// Captures a common usage pattern for allocators.
        ///
        /// # Safety
        ///
        /// This function is unsafe because undefined behavior can result
        /// if the caller does not ensure both:
        ///
        /// * `ptr` must denote a block of memory currently allocated via this
        ///   allocator
        ///
        /// * the layout of `[T; n]` must *fit* that block of memory.
        unsafe fn dealloc_array<T>(
            &mut self,
            ptr: NonNull<T>,
            n: usize,
        ) -> Result<()>
        where
            Self: Sized,
        {
            match Layout::array::<T>(n) {
                Ok(k) if k.size() > 0 => {
                    self.dealloc(ptr.cast(), k);
                    Ok(())
                },
                _ => Err(anyhow::anyhow!("alloc error")),
            }
        }
    }
}

unsafe impl<'a> alloc::Alloc for &'a Bump {
    #[inline(always)]
    unsafe fn alloc(&mut self, layout: Layout) -> Result<NonNull<u8>> {
        self.try_alloc_layout(layout)
    }

    #[inline]
    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: Layout) {
        // If the pointer is the last allocation we made, we can reuse the
        // bytes, otherwise they are simply leaked -- at least until
        // somebody calls reset().
        if self.is_last_allocation(ptr) {
            let ptr = NonNull::new_unchecked(ptr.as_ptr().add(layout.size()));
            self.current_chunk_footer.get().as_ref().ptr.set(ptr);
        }
    }

    #[inline]
    unsafe fn realloc(
        &mut self,
        ptr: NonNull<u8>,
        layout: Layout,
        new_size: usize,
    ) -> Result<NonNull<u8>> {
        let old_size = layout.size();

        if old_size == 0 {
            return self.alloc(layout);
        }

        if new_size <= old_size {
            if self.is_last_allocation(ptr)
                // Only reclaim the excess space (which requires a copy) if it
                // is worth it: we are actually going to recover "enough" space
                // and we can do a non-overlapping copy.
                && new_size <= old_size / 2
            {
                let delta = old_size - new_size;
                let footer = self.current_chunk_footer.get();
                let footer = footer.as_ref();
                footer.ptr.set(NonNull::new_unchecked(
                    footer.ptr.get().as_ptr().add(delta),
                ));
                let new_ptr = footer.ptr.get();
                // NB: we know it is non-overlapping because of the size check
                // in the `if` condition.
                ptr::copy_nonoverlapping(
                    ptr.as_ptr(),
                    new_ptr.as_ptr(),
                    new_size,
                );
                return Ok(new_ptr);
            } else {
                return Ok(ptr);
            }
        }

        if self.is_last_allocation(ptr) {
            // Try to allocate the delta size within this same block so we can
            // reuse the currently allocated space.
            let delta = new_size - old_size;
            if let Some(p) = self.try_alloc_layout_fast(layout_from_size_align(
                delta,
                layout.align(),
            )) {
                ptr::copy(ptr.as_ptr(), p.as_ptr(), old_size);
                return Ok(p);
            }
        }

        // Fallback: do a fresh allocation and copy the existing data into it.
        let new_layout = layout_from_size_align(new_size, layout.align());
        let new_ptr = self.try_alloc_layout(new_layout)?;
        ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_size);
        Ok(new_ptr)
    }
}
