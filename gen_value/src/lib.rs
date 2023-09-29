// Copyright 2023 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![doc = include_str!("../README.md")]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(
    rust_2018_idioms,
    missing_docs,
    missing_debug_implementations,
    unused_lifetimes,
    unused_qualifications
)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(all(feature = "alloc", not(feature = "std")))]
extern crate alloc;

use core::fmt;

pub mod index;
pub mod unmanaged;
pub mod vec;

/// A type which can attempt to return the smallest value which is still bigger
/// than the current value.
///
/// It is used for index and generation type parameters to find the next index
/// or the next generation respectively.
///
/// # Examples
///
/// An implementation of `Incrementable` has been made for all integer types.
///
/// ```
/// use gen_value::Incrementable;
///
/// let value: u32 = 1;
/// assert_eq!(value.next(), Some(2));
/// assert_eq!(u32::MAX.next(), None);
/// ```
pub trait Incrementable: PartialOrd + Sized {
    /// Returns the next value, if available.
    fn next(&self) -> Option<Self>;

    /// Returns the maximum value, if available.
    ///
    /// For generations, the maximum value serves as an indicator that the index
    /// can no longer be used (tombstone value). The last generation used would
    /// be `max() - 1`.
    fn max() -> Option<Self>;
}

/// Makes an Incremental implementation for an integer type.
macro_rules! make_incremental_int_impl {
    ($ty:ident) => {
        impl Incrementable for $ty {
            fn next(&self) -> Option<Self> {
                self.checked_add(1)
            }

            fn max() -> Option<Self> {
                Some(Self::MAX)
            }
        }
    };
}

make_incremental_int_impl!(u8);
make_incremental_int_impl!(u16);
make_incremental_int_impl!(u32);
make_incremental_int_impl!(u64);
make_incremental_int_impl!(usize);
make_incremental_int_impl!(i8);
make_incremental_int_impl!(i16);
make_incremental_int_impl!(i32);
make_incremental_int_impl!(i64);
make_incremental_int_impl!(isize);

#[derive(Debug)]
enum ErrorCode {
    IndexOutOfBounds,
    LessThanExistingGeneration,
    NotEqualGeneration,
    CannotAllocateGenerationalIndex,
    AlreadyEqualGeneration,
}

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorCode::IndexOutOfBounds => f.write_str("index out of bounds"),
            ErrorCode::LessThanExistingGeneration => f.write_str(
                "generational index's generation is less than the existing element's generation",
            ),
            ErrorCode::NotEqualGeneration => {
                f.write_str("element's generation does not equal the generation index's generation")
            }
            ErrorCode::CannotAllocateGenerationalIndex => {
                f.write_str("cannot allocate a generational index")
            }
            ErrorCode::AlreadyEqualGeneration => {
                f.write_str("generation is already equal to existing generation")
            }
        }
    }
}

/// Errors from calling [`GenVec`] and [`UnmanagedGenVec`][crate::unmanaged::UnmanagedGenVec] functions.
#[derive(Debug)]
pub struct Error {
    code: ErrorCode,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> core::fmt::Result {
        fmt::Display::fmt(&self.code, f)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

impl Error {
    #[inline]
    pub(crate) fn index_out_of_bounds() -> Self {
        Error {
            code: ErrorCode::IndexOutOfBounds,
        }
    }

    /// Index is out of bounds.
    #[must_use]
    pub fn is_index_out_of_bounds(&self) -> bool {
        matches!(self.code, ErrorCode::IndexOutOfBounds)
    }

    #[inline]
    pub(crate) fn less_than_existing_generation() -> Self {
        Error {
            code: ErrorCode::LessThanExistingGeneration,
        }
    }

    /// Generation is less than generation associated with element.
    #[must_use]
    pub fn is_generation_less_than_existing(&self) -> bool {
        matches!(self.code, ErrorCode::LessThanExistingGeneration)
    }

    #[inline]
    pub(crate) fn not_equal_generation() -> Self {
        Error {
            code: ErrorCode::NotEqualGeneration,
        }
    }

    /// Generations are not equal.
    #[must_use]
    pub fn is_not_equal_generation_error(&self) -> bool {
        matches!(self.code, ErrorCode::NotEqualGeneration)
    }

    #[inline]
    pub(crate) fn cannot_allocate_generational_index() -> Self {
        Error {
            code: ErrorCode::CannotAllocateGenerationalIndex,
        }
    }

    /// Could not allocate a generation index.
    #[must_use]
    pub fn is_generational_index_allocation_error(&self) -> bool {
        matches!(self.code, ErrorCode::CannotAllocateGenerationalIndex)
    }

    #[inline]
    pub(crate) fn already_equal_generation() -> Self {
        Error {
            code: ErrorCode::AlreadyEqualGeneration,
        }
    }

    /// Generations are already equal.
    #[must_use]
    pub fn is_already_equal_generation_error(&self) -> bool {
        matches!(self.code, ErrorCode::AlreadyEqualGeneration)
    }
}

pub use vec::GenVec;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn incrementable_overflow() {
        assert_eq!(u8::MAX.next(), None);
        assert_eq!(u16::MAX.next(), None);
        assert_eq!(u32::MAX.next(), None);
        assert_eq!(u64::MAX.next(), None);
        assert_eq!(usize::MAX.next(), None);
        assert_eq!(i8::MAX.next(), None);
        assert_eq!(i16::MAX.next(), None);
        assert_eq!(i32::MAX.next(), None);
        assert_eq!(i64::MAX.next(), None);
        assert_eq!(isize::MAX.next(), None);
    }
}
