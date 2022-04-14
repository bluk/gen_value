// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! `Vec` indexed with externally managed generational indexes.

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use crate::Error;

/// `Vec` indexed with externally managed generational indexes.
///
/// `UnmanagedGenVec` does not manage its own indexes. An external source must
/// allocate and deallocate indexes with generations appropriately.
///
/// If a single `Vec` with generational indexes is required, then using
/// [`GenVec`][crate::vec::GenVec] is useful. If generational indexes must be
/// allocated and deallocated externally or if multiple vectors are required,
/// then the [`Allocator`][crate::index::Allocator] and `UnmanagedGenVec` may be
/// more useful.
///
/// # Important
///
/// The generation at an index in the inner `Vec` should always be greater than or
/// equal to any generational index's generation for the same index.
///
/// # Type Parameters
///
/// ## T
///
/// `T` is the element value type like the `T` in `Vec<T>`.
///
/// ## G
///
/// `G` is the generation type. `G` is usually a type like [u16] or [u32].
/// By default, G is a [u16].
///
/// Generation types must implement:
///
/// * [`PartialOrd`]
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
/// ## I
///
/// `I` is the index type required in most functions. `I` is turned into a
/// [usize] to index into the inner `Vec`.
///
/// Index types must implement:
///
/// * `Into<usize>`
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[allow(clippy::module_name_repetitions)]
pub struct UnmanagedGenVec<T, G = u16> {
    inner: Vec<(G, T)>,
}

impl<T, G> UnmanagedGenVec<T, G> {
    /// Constructs a new inner [`Vec`].
    ///
    /// See [`Vec::new`] for additional information.
    #[must_use]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    /// Constructs an inner [`Vec`] with the given capacity.
    ///
    /// See [`Vec::with_capacity`] for additional information.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Vec::with_capacity(capacity),
        }
    }

    /// Returns the length of the inner [`Vec`].
    ///
    /// See [`Vec::len`] for additional information.
    #[must_use]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns true if the innner [`Vec`] is empty.
    ///
    /// See [`Vec::is_empty`] for additional information.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Returns the capacity of the inner [`Vec`].
    ///
    /// See [`Vec::capacity`] for additional information.
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Reserves additional capacity of the inner [`Vec`].
    ///
    /// See [`Vec::reserve`] for additional information.
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional);
    }

    /// Reserves additional capacity of the inner [`Vec`].
    ///
    /// See [`Vec::reserve_exact`] for additional information.
    pub fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional);
    }
}

impl<T, G> Default for UnmanagedGenVec<T, G> {
    fn default() -> Self {
        Self {
            inner: Vec::default(),
        }
    }
}

impl<T, G> UnmanagedGenVec<T, G> {
    /// Pushes a generation and value to the end of the inner [`Vec`].
    ///
    /// See [`Vec::push`] for additional information.
    pub fn push(&mut self, generation: G, value: T) {
        self.inner.push((generation, value));
    }

    /// Returns true if an element exists for the generational index.
    pub fn contains_index<I>(&self, gen_index: (I, G)) -> bool
    where
        I: Into<usize>,
        G: PartialEq,
    {
        self.get(gen_index).is_ok()
    }

    /// Returns a reference to the element at the given index if the generation matches.
    ///
    /// See [`slice::get`] for additional information.
    ///
    /// # Errors
    ///
    /// Errors are returned if:
    ///
    /// * the index is out of bounds
    /// * the generation of the generational index is less than the generation associated with the element
    pub fn get<I>(&self, gen_index: (I, G)) -> Result<&T, Error>
    where
        I: Into<usize>,
        G: PartialEq,
    {
        self.inner
            .get(gen_index.0.into())
            .ok_or_else(Error::index_out_of_bounds)
            .map(|(gen, elem)| (gen_index.1 == *gen).then(|| elem))?
            .ok_or_else(Error::not_equal_generation)
    }

    /// Returns a mutable reference to the element at the given index if the generation matches.
    ///
    /// See [`slice::get_mut`] for additional information.
    ///
    /// # Errors
    ///
    /// Errors are returned if:
    ///
    /// * the index is out of bounds
    /// * the generation of the generational index is less than the generation associated with the element
    pub fn get_mut<I>(&mut self, gen_index: (I, G)) -> Result<&mut T, Error>
    where
        I: Into<usize>,
        G: PartialEq,
    {
        let elem = self
            .inner
            .get_mut(gen_index.0.into())
            .ok_or_else(Error::index_out_of_bounds)?;
        if elem.0 == gen_index.1 {
            Ok(&mut elem.1)
        } else {
            Err(Error::not_equal_generation())
        }
    }

    /// Returns a reference to the element at the given index.
    ///
    /// See [`slice::get_unchecked`] for additional information.
    ///
    /// # Safety
    ///
    /// There is no bounds check and no generation check performed. If the index is out of bounds, undefined behavior will occur.
    pub unsafe fn get_unchecked<I>(&self, gen_index: (I, G)) -> &T
    where
        I: Into<usize>,
    {
        &self.inner.get_unchecked(gen_index.0.into()).1
    }

    /// Returns a mutable reference to the element at the given index.
    ///
    /// See [`slice::get_unchecked_mut`] for additional information.
    ///
    /// # Safety
    ///
    /// There is no bounds check and no generation check performed. If the index is out of bounds, undefined behavior will occur.
    pub unsafe fn get_unchecked_mut<I>(&mut self, gen_index: (I, G)) -> &mut T
    where
        I: Into<usize>,
    {
        &mut self.inner.get_unchecked_mut(gen_index.0.into()).1
    }

    /// Returns the generation associated with the element at the index.
    ///
    /// Returns `None` if the index is out of bounds.
    pub fn get_gen<I>(&self, index: I) -> Option<&G>
    where
        I: Into<usize>,
    {
        self.inner.get(index.into()).map(|(gen, _value)| gen)
    }

    fn internal_set(&mut self, index: usize, generation: G, value: T) -> Result<(G, T), Error>
    where
        G: PartialOrd,
    {
        let elem = self
            .inner
            .get_mut(index)
            .ok_or_else(Error::index_out_of_bounds)?;
        if elem.0 <= generation {
            let prev_value = core::mem::replace(elem, (generation, value));
            Ok(prev_value)
        } else {
            Err(Error::less_than_existing_generation())
        }
    }

    /// Sets a value at the given index if the generation is greater than or
    /// equal to the generation associated with the existing element.
    ///
    /// Returns the previous generation and the value for the element if successful.
    ///
    /// # Errors
    ///
    /// Errors are returned if:
    ///
    /// * the index is out of bounds
    /// * the generation of the generational index is less than the generation associated with the element
    pub fn set<I>(&mut self, gen_index: (I, G), value: T) -> Result<(G, T), Error>
    where
        G: PartialOrd,
        I: Into<usize>,
    {
        self.internal_set(gen_index.0.into(), gen_index.1, value)
    }

    /// Sets or pushes the element at the index if the generation is equal to or
    /// greater than the existing generation associated with the element.
    ///
    /// Returns the previous generation and the value for the element if replacing an existing value.
    ///
    /// # Errors
    ///
    /// Errors are returned if:
    ///
    /// * the index is out of bounds
    /// * the generation of the generational index is less than the generation associated with the element
    ///
    /// # Panics
    ///
    /// * if the index is greater than the length of the inner vector
    pub fn set_or_push<I>(&mut self, gen_index: (I, G), value: T) -> Result<Option<(G, T)>, Error>
    where
        G: PartialOrd,
        I: Into<usize>,
    {
        let (index, generation) = gen_index;
        let index = index.into();
        assert!(index <= self.inner.len());
        if index < self.len() {
            self.internal_set(index, generation, value).map(Some)
        } else {
            debug_assert_eq!(index, self.len());
            self.push(generation, value);
            Ok(None)
        }
    }

    /// Sets the generation for an index if the generation is greater than
    /// the existing generation associated with the element.
    ///
    /// Returns the previous generation if successful.
    ///
    /// # Errors
    ///
    /// Errors are returned if:
    ///
    /// * the index is out of bounds
    /// * the generation is less than or equal to the existing generation associated with
    /// the element
    pub fn set_gen<I>(&mut self, gen_index: (I, G)) -> Result<G, Error>
    where
        G: PartialOrd,
        I: Into<usize>,
    {
        let (index, generation) = gen_index;
        let elem = self
            .inner
            .get_mut(index.into())
            .ok_or_else(Error::index_out_of_bounds)?;
        if elem.0 < generation {
            let prev_value = core::mem::replace(&mut elem.0, generation);
            Ok(prev_value)
        } else if elem.0 == generation {
            Err(Error::already_equal_generation())
        } else {
            Err(Error::less_than_existing_generation())
        }
    }
}

impl<T, G, I> core::ops::Index<(I, G)> for UnmanagedGenVec<T, G>
where
    I: Into<usize>,
    G: PartialEq,
{
    type Output = T;

    fn index(&self, gen_index: (I, G)) -> &Self::Output {
        let idx = gen_index.0.into();
        let (cur_gen, elem) = &self.inner[idx];
        let expected_gen = gen_index.1;
        if expected_gen == *cur_gen {
            elem
        } else {
            panic!("GenIndex::Generation is not equivalent");
        }
    }
}

// IndexMut is not implemented for UnmanagedGenVec because the behavior when accessing with an unequal generation is difficult.
// If the element stored in the vec has a different generation than gen_index, then:
//
// let gen_vec = GenVec::default();
// let value = &mut gen_vec[gen_index];
// *value = new_value;
// // and
// gen_vec[gen_index] = new_value;
// // become confusing
