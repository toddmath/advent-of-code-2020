pub use anyhow::{self, bail, Context, Error, Result};
pub use bitvec::prelude::*;
pub use itertools::{iproduct, izip, traits::HomogeneousTuple, Itertools};
pub use lazy_static::lazy_static;
pub use maplit::{btreemap, btreeset, hashmap, hashset};
pub use num_integer::{
    average_ceil, average_floor, binomial, cbrt, div_ceil, div_floor,
    div_mod_floor, div_rem, gcd, gcd_lcm, lcm, mod_floor, multinomial,
    nth_root, sqrt, Average, Integer, Roots,
};
pub use num_traits::{
    Num, NumAssign, NumAssignOps, NumAssignRef, NumCast, NumOps, NumRef, RefNum,
};
pub use predicates::prelude::*;
pub use rayon::prelude::*;
pub use scan_fmt::scan_fmt;

// pub use num_derive::{
// Float, FromPrimitive, Num, NumCast, NumOps, One, ToPrimitive, Zero,
// };
// pub use num_traits::{AsPrimitive, Bounded, Zero, One, Float, CheckedAdd,
// CheckedDiv, CheckedMul, CheckedNeg, CheckedRem, CheckedShl, CheckedShr,
// CheckedSub, FloatConst};

///////////////////////////////////////////////////////////////////////////////
////
//// * workspace
////
///////////////////////////////////////////////////////////////////////////////
pub use aoc_runner::{
    parse_string, parse_to, read_to_iter, read_to_vec, Reader, Solver,
};
pub use common::{
    either, match_map, parse_int_fast, parse_int_fast_skip_custom, smallvec,
    try_left, try_right, tuple, Array, ByteSliceExt, Either, HashMap, HashSet,
    IterExt, Left, Right, SliceExt, SmallVec, ToSmallVec, TupleElements,
    Unpeekable,
};

///////////////////////////////////////////////////////////////////////////////
////
//// * stdlib
////
///////////////////////////////////////////////////////////////////////////////
pub use std::{
    borrow::{Borrow, BorrowMut},
    cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd},
    collections::VecDeque,
    convert::{AsMut, AsRef, From, TryFrom, TryInto},
    fmt::{self, Debug, Display, Formatter},
    hash::{Hash, Hasher},
    io::prelude::*,
    iter::{
        from_fn, repeat, DoubleEndedIterator, ExactSizeIterator, FromIterator,
        FusedIterator, InPlaceIterable, IntoIterator,
    },
    ops::{Deref, DerefMut, Drop, Range, RangeBounds},
    slice::{self, Iter as SliceIter, IterMut as SliceIterMut, SliceIndex},
    str::FromStr,
};
