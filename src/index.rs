// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Generational indexes.

use core::marker::PhantomData;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use crate::Incrementable;

/// Generational index allocator.
///
/// Allocators are primarily used to [allocate][Allocator::alloc] new
/// generational indexes. If a generational index is no longer useful (e.g. the
/// entity using the index is dropped), then the generational index can be
/// returned to the allocator via [dealloc][Allocator::dealloc]. By
/// deallocating the index, the same index can be used with a newer generation for
/// a new generational index.
///
/// # Type Parameters
///
/// ## `G`
///
/// `G` is the generation type. `G` is usually a type like [u16] or [u32].
/// By default, G is a [u16].
///
/// Generation types must implement:
///
/// * [`Incrementable`]
/// * [`Default`]
///
/// The range of values for `G` determines how many generations a single index
/// can be used. Assume a [u8] is used and a single index is allocated and
/// deallocated 256 times. After the 256th allocation, the index will never be
/// allocated again. For [`GenVec`][crate::vec::GenVec], an index which will
/// never be re-used is essentially equivalent to wasted memory which will not
/// be reclaimed.
///
/// Assuming a single index is allocated and deallocated every second, a [u16]
/// would take 2^16 seconds to exhaust an index which is roughly 18 hours. A
/// [u32] would take 2^32 seconds which is more than 136 years.
///
/// ## `I`
///
/// `I` is the index type. `I` is usually a type like [usize]. By default, `I`
/// is a [usize].
///
/// Index types must implement:
///
/// * [`Incrementable`]
/// * `Into<usize>`
///
/// The range of values for `I` determines the maximum limit on how many
/// concurrent entities may exist. If a [u8] is used, a maximum of `256`
/// values exist at any point in time.
///
/// ## `GenIndex`
///
/// `GenIndex` is the type which the generational index should be returned as. A tuple
/// like `(I, G)` can be used or a custom type. By default, `(I, G)` is used.
///
/// The generational index type is generally treated like an opaque identifier.
/// While a tuple is useful, a custom type may be desired so a generational
/// index is only used with collections which take the custom type.
///
/// For the [alloc][Self::alloc] and [dealloc][Self::dealloc] methods `GenIndex` must
/// implement:
///
/// * `From<(I, G)> for GenIndex`
/// * `Into<(I, G)> for GenIndex`
#[derive(Debug)]
pub struct Allocator<G = u16, I = usize, GenIndex = (I, G)> {
    next_index: Option<I>,
    avail_gen_indexes: Vec<GenIndex>,
    gen_ty: PhantomData<G>,
}

impl<G, I, GenIndex> Allocator<G, I, GenIndex> {
    /// Constructs an allocator with the default index value as the initial value.
    ///
    /// # Examples
    ///
    /// An allocator using [u16] for the generation type, the default [usize]
    /// for the index type. and the default tuple type `(index type, generation type)`
    /// for the generational index type.
    ///
    /// ```
    /// use gen_value::index::Allocator;
    ///
    /// let mut gen_index_alloc = Allocator::<u16>::new();
    /// assert_eq!(gen_index_alloc.alloc(), Some((0usize, 0u16)));
    /// ```
    ///
    /// An allocator using [u16] for the generation type, the [u8]
    /// for the index type. and the tuple type `(u8, u16)`
    /// for the generational index type.
    ///
    /// ```
    /// use gen_value::index::Allocator;
    ///
    /// let mut gen_index_alloc = Allocator::<u16, u8, (u8, u16)>::new();
    /// assert_eq!(gen_index_alloc.alloc(), Some((0u8, 0u16)));
    /// ```
    ///
    /// An allocator using a custom type for the generational index:
    ///
    /// ```
    /// use gen_value::index::Allocator;
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct MyGenIndex {
    ///   index: usize,
    ///   gen: u32,
    /// }
    ///
    /// impl From<(usize, u32)> for MyGenIndex {
    ///   fn from(value: (usize, u32)) -> Self {
    ///     Self {
    ///       index: value.0,
    ///       gen: value.1,
    ///     }
    ///   }
    /// }
    ///
    /// impl From<MyGenIndex> for (usize, u32) {
    ///   fn from(value: MyGenIndex) -> Self {
    ///     (value.index, value.gen)
    ///   }
    /// }
    ///
    /// let mut gen_index_alloc = Allocator::<u32, usize, MyGenIndex>::new();
    /// assert_eq!(gen_index_alloc.alloc(), Some(MyGenIndex { index: 0usize, gen: 0u32 }));
    /// ```
    #[must_use]
    pub fn new() -> Self
    where
        I: Default,
    {
        Self::default()
    }

    /// Constructs an allocator with an initial index value.
    ///
    /// # Examples
    ///
    /// An allocator using [u16] for the generation type, the [u8]
    /// for the index type. and the default tuple type `(index type, generation type)`
    /// for the generational index type.
    ///
    /// The initial index value is `2u8`.
    ///
    /// ```
    /// use gen_value::index::Allocator;
    ///
    /// let mut gen_index_alloc = Allocator::<u16, u8>::with_initial_index(2u8);
    /// assert_eq!(gen_index_alloc.alloc(), Some((2u8, 0u16)));
    /// ```
    pub fn with_initial_index(index: I) -> Self {
        Self {
            next_index: Some(index),
            avail_gen_indexes: Vec::default(),
            gen_ty: PhantomData,
        }
    }
}

impl<G, I, GenIndex> Default for Allocator<G, I, GenIndex>
where
    I: Default,
{
    fn default() -> Self {
        Self {
            next_index: Some(I::default()),
            avail_gen_indexes: Vec::default(),
            gen_ty: PhantomData,
        }
    }
}

impl<G, I, GenIndex> Allocator<G, I, GenIndex>
where
    GenIndex: From<(I, G)>,
{
    /// Returns the next available generational index.
    ///
    /// Returns `None` if there are no currently available generational indexes.
    ///
    /// # Examples
    ///
    /// An allocator using [u16] for the generation type, the [u8]
    /// for the index type. and the default tuple type `(index type, generation type)`
    /// for the generational index type.
    ///
    /// ```
    /// use gen_value::index::Allocator;
    ///
    /// let mut gen_index_alloc = Allocator::<u16, u8>::default();
    /// assert_eq!(gen_index_alloc.alloc(), Some((0u8, 0u16)));
    /// ```
    ///
    /// An allocator using a custom type for the generational index:
    ///
    /// ```
    /// use gen_value::index::Allocator;
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct MyGenIndex {
    ///   index: usize,
    ///   gen: u32,
    /// }
    ///
    /// impl From<(usize, u32)> for MyGenIndex {
    ///   fn from(value: (usize, u32)) -> Self {
    ///     Self {
    ///       index: value.0,
    ///       gen: value.1,
    ///     }
    ///   }
    /// }
    ///
    /// impl From<MyGenIndex> for (usize, u32) {
    ///   fn from(value: MyGenIndex) -> Self {
    ///     (value.index, value.gen)
    ///   }
    /// }
    ///
    /// let mut gen_index_alloc = Allocator::<u32, usize, MyGenIndex>::default();
    /// assert_eq!(gen_index_alloc.alloc(), Some(MyGenIndex { index: 0usize, gen: 0u32 }));
    /// ```
    #[must_use]
    pub fn alloc(&mut self) -> Option<GenIndex>
    where
        G: Default,
        I: Incrementable,
    {
        self.avail_gen_indexes.pop().or_else(|| {
            if let Some(index) = self.next_index.take() {
                self.next_index = index.next();
                Some(GenIndex::from((index, G::default())))
            } else {
                None
            }
        })
    }

    /// Informs the allocator that an index is no longer being used.
    ///
    /// The generator can re-use the index with an increment in the generation.
    /// It allows an index in a collection to be reused (which reduces memory
    /// allocations and copies).
    ///
    /// A preview of the next generation of the index is returned, if available.
    /// The generation may not be able to be incremented so `None` could be
    /// returned.
    ///
    /// The return value is a preview of the next generation of the index.
    /// It could be used to increment the generation at a collection's
    /// index. By incrementing the generation, the original index can not be
    /// used to access data from the collection.
    ///
    /// # Safety
    ///
    /// It is a program logic bug to dealloc the same generational index value
    /// more than once.
    ///
    /// If the same value is deallocated, the allocator may return the same
    /// generational index multiple times. The generation associated with the
    /// index may be invalid or repeated.
    ///
    /// # Examples
    ///
    /// An allocator using [u16] for the generation type, the [u8]
    /// for the index type. and the default tuple type `(index type, generation type)`
    /// for the generational index type.
    ///
    /// ```
    /// use gen_value::index::Allocator;
    ///
    /// let mut gen_index_alloc = Allocator::<u16, u8>::default();
    ///
    /// let gen_index_0 = gen_index_alloc.alloc().unwrap();
    /// assert_eq!(gen_index_0, (0u8, 0u16));
    ///
    /// let gen_index_1 = gen_index_alloc.alloc();
    /// assert_eq!(gen_index_1, Some((1u8, 0u16)));
    ///
    /// // Dealloc the first generational index
    /// let next_gen_index = gen_index_alloc.dealloc(gen_index_0);
    /// assert_eq!(next_gen_index, Some(&(0u8, 1u16)));
    ///
    /// // Generation increased
    /// let gen_index_0_again = gen_index_alloc.alloc();
    /// assert_eq!(gen_index_0_again, Some((0u8, 1u16)));
    /// ```
    ///
    /// An allocator using a custom type for the generational index:
    ///
    /// ```
    /// use gen_value::index::Allocator;
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct MyGenIndex {
    ///   index: usize,
    ///   gen: u32,
    /// }
    ///
    /// impl From<(usize, u32)> for MyGenIndex {
    ///   fn from(value: (usize, u32)) -> Self {
    ///     Self {
    ///       index: value.0,
    ///       gen: value.1,
    ///     }
    ///   }
    /// }
    ///
    /// impl From<MyGenIndex> for (usize, u32) {
    ///   fn from(value: MyGenIndex) -> Self {
    ///     (value.index, value.gen)
    ///   }
    /// }
    ///
    /// let mut gen_index_alloc = Allocator::<u32, usize, MyGenIndex>::default();
    ///
    /// let gen_index_0 = gen_index_alloc.alloc().unwrap();
    /// assert_eq!(gen_index_0, MyGenIndex { index: 0usize, gen: 0u32 });
    ///
    /// let gen_index_1 = gen_index_alloc.alloc();
    /// assert_eq!(gen_index_1, Some(MyGenIndex { index: 1usize, gen: 0u32 }));
    ///
    /// // Dealloc the first generational index
    /// let next_gen_index = gen_index_alloc.dealloc(gen_index_0);
    /// assert_eq!(next_gen_index, Some(&MyGenIndex { index: 0usize, gen: 1u32 }));
    ///
    /// // Generation increased
    /// let gen_index_0_again = gen_index_alloc.alloc();
    /// assert_eq!(gen_index_0_again, Some(MyGenIndex { index: 0usize, gen: 1u32  }));
    /// ```
    pub fn dealloc(&mut self, gen_index: GenIndex) -> Option<&GenIndex>
    where
        GenIndex: Into<(I, G)>,
        G: Incrementable,
    {
        let gen_index: (I, G) = gen_index.into();

        if let Some(avail_gen_index) = gen_index
            .1
            .next()
            .map(|new_gen| GenIndex::from((gen_index.0, new_gen)))
        {
            self.avail_gen_indexes.push(avail_gen_index);
            self.avail_gen_indexes.last()
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alloc_with_tuple() {
        let mut gen_idx_alloc = Allocator::<u32>::default();

        let gen_idx_0 = gen_idx_alloc.alloc();
        let gen_idx_0 = gen_idx_0.unwrap();
        {
            assert_eq!(gen_idx_0.0, 0);
            assert_eq!(gen_idx_0.1, 0);
        }

        {
            let gen_idx_1 = gen_idx_alloc.alloc();
            let gen_idx_1 = gen_idx_1.unwrap();
            assert_eq!(gen_idx_1.0, 1);
            assert_eq!(gen_idx_1.1, 0);
        }

        gen_idx_alloc.dealloc(gen_idx_0);

        {
            let gen_idx_0_again = gen_idx_alloc.alloc();
            let gen_idx_0_again = gen_idx_0_again.unwrap();
            assert_eq!(gen_idx_0_again.0, 0);
            assert_eq!(gen_idx_0_again.1, 1);
        }
    }

    #[test]
    fn test_alloc_with_custom_type() {
        struct MyIndex {
            index: usize,
            gen: u32,
        }
        impl From<(usize, u32)> for MyIndex {
            fn from(value: (usize, u32)) -> Self {
                Self {
                    index: value.0,
                    gen: value.1,
                }
            }
        }
        impl From<MyIndex> for (usize, u32) {
            fn from(value: MyIndex) -> Self {
                (value.index, value.gen)
            }
        }

        let mut gen_idx_alloc = Allocator::<u32, usize, MyIndex>::default();

        let gen_idx_0 = gen_idx_alloc.alloc();
        let gen_idx_0 = gen_idx_0.unwrap();
        {
            assert_eq!(gen_idx_0.index, 0);
            assert_eq!(gen_idx_0.gen, 0);
        }

        {
            let gen_idx_1 = gen_idx_alloc.alloc();
            let gen_idx_1 = gen_idx_1.unwrap();
            assert_eq!(gen_idx_1.index, 1);
            assert_eq!(gen_idx_1.gen, 0);
        }

        gen_idx_alloc.dealloc(gen_idx_0);

        {
            let gen_idx_0_again = gen_idx_alloc.alloc();
            let gen_idx_0_again = gen_idx_0_again.unwrap();
            assert_eq!(gen_idx_0_again.index, 0);
            assert_eq!(gen_idx_0_again.gen, 1);
        }
    }
}
