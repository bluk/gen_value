// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! `Vec` indexed with externally managed generational indexes.

use core::{cmp::Ordering, marker::PhantomData};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use crate::{Error, Incrementable};

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
/// # Safety
///
/// The generation at an index in the inner `Vec` should always be greater than or
/// equal to any generational index's generation for the same index.
///
/// If the generation has a maximum value (e.g. `u8::MAX`), then the maximum value
/// should serve as a tombstone to indicate that the index cannot be used.
/// Any generational index with the maximum generation should never
/// be used for any method except [`set_gen`][UnmanagedGenVec::set_gen].
///
/// # Type Parameters
///
/// ## `T`
///
/// `T` is the element value type like the `T` in `Vec<T>`.
///
/// ## `G`
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
/// deallocated 255 times. After the 255th allocation, the index will never be
/// allocated again. For [`GenVec`][crate::vec::GenVec], an index which will
/// never be re-used is essentially equivalent to wasted memory which will not
/// be reclaimed.
///
/// Note that for a [u8], the maximum value (255) serves as a tombstone marker
/// indicating that the index can no longer be used (otherwise a generational
/// index with generation 255 could always access the value).
///
/// Assuming a single index is allocated and deallocated every second, a [u16]
/// would take (2^16 - 1) seconds to exhaust an index which is roughly 18 hours. A
/// [u32] would take (2^32 - 1) seconds which is more than 136 years.
///
/// ## `I`
///
/// `I` is the index type required in most functions. `I` is turned into a
/// [usize] to index into the inner `Vec`. By default, `I` is a [usize].
///
/// Index types must implement:
///
/// * `Into<usize>`
///
/// The range of values for `I` determines the maximum limit on how many
/// concurrent entities may exist. If a [u8] is used, a maximum of `256`
/// values exist at any point in time.
///
/// ## `GenIndex`
///
/// `GenIndex` is the type which the generational index should be. A tuple
/// like `(I, G)` can be used or a custom type. By default, `(I, G)` is used.
///
/// The generational index type is generally treated like an opaque identifier.
/// While a tuple is useful, a custom type may be desired so a generational
/// index is only used with collections which take the custom type.
///
/// `GenIndex` types must implement:
///
/// * `Into<(I, G)> for GenIndex`
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[allow(clippy::module_name_repetitions)]
pub struct UnmanagedGenVec<T, G = u16, I = usize, GenIndex = (I, G)> {
    inner: Vec<(G, T)>,
    index_ty: PhantomData<I>,
    gen_index_ty: PhantomData<GenIndex>,
}

impl<T, G, I, GenIndex> UnmanagedGenVec<T, G, I, GenIndex> {
    /// Constructs a new inner [`Vec`].
    ///
    /// See [`Vec::new`] for additional information.
    #[must_use]
    pub fn new() -> Self {
        Self {
            inner: Vec::new(),
            index_ty: PhantomData,
            gen_index_ty: PhantomData,
        }
    }

    /// Constructs an inner [`Vec`] with the given capacity.
    ///
    /// See [`Vec::with_capacity`] for additional information.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Vec::with_capacity(capacity),
            index_ty: PhantomData,
            gen_index_ty: PhantomData,
        }
    }

    /// Returns the length of the inner [`Vec`].
    ///
    /// See [`Vec::len`] for additional information.
    #[must_use]
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns true if the innner [`Vec`] is empty.
    ///
    /// See [`Vec::is_empty`] for additional information.
    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Returns the capacity of the inner [`Vec`].
    ///
    /// See [`Vec::capacity`] for additional information.
    #[must_use]
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Reserves additional capacity of the inner [`Vec`].
    ///
    /// See [`Vec::reserve`] for additional information.
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional);
    }

    /// Reserves additional capacity of the inner [`Vec`].
    ///
    /// See [`Vec::reserve_exact`] for additional information.
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional);
    }
}

impl<T, G, I, GenIndex> Default for UnmanagedGenVec<T, G, I, GenIndex> {
    fn default() -> Self {
        Self {
            inner: Vec::default(),
            index_ty: PhantomData,
            gen_index_ty: PhantomData,
        }
    }
}

impl<T, G, I, GenIndex> UnmanagedGenVec<T, G, I, GenIndex> {
    /// Pushes a generation and value to the end of the inner [`Vec`].
    ///
    /// See [`Vec::push`] for additional information.
    #[inline]
    pub fn push(&mut self, generation: G, value: T) {
        self.inner.push((generation, value));
    }

    /// Returns true if an element exists for the generational index.
    #[inline]
    pub fn contains_index(&self, gen_index: GenIndex) -> bool
    where
        GenIndex: Into<(I, G)>,
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
    /// * the generation of the generational index is not equal to the generation associated with the element
    pub fn get(&self, gen_index: GenIndex) -> Result<&T, Error>
    where
        GenIndex: Into<(I, G)>,
        I: Into<usize>,
        G: PartialEq,
    {
        let gen_index = gen_index.into();
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
    /// * the generation of the generational index is not equal to the generation associated with the element
    pub fn get_mut(&mut self, gen_index: GenIndex) -> Result<&mut T, Error>
    where
        GenIndex: Into<(I, G)>,
        I: Into<usize>,
        G: PartialEq,
    {
        let gen_index = gen_index.into();
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
    #[inline]
    pub unsafe fn get_unchecked(&self, gen_index: GenIndex) -> &T
    where
        GenIndex: Into<(I, G)>,
        I: Into<usize>,
    {
        let gen_index = gen_index.into();
        &self.inner.get_unchecked(gen_index.0.into()).1
    }

    /// Returns a mutable reference to the element at the given index.
    ///
    /// See [`slice::get_unchecked_mut`] for additional information.
    ///
    /// # Safety
    ///
    /// There is no bounds check and no generation check performed. If the index is out of bounds, undefined behavior will occur.
    #[inline]
    pub unsafe fn get_unchecked_mut(&mut self, gen_index: GenIndex) -> &mut T
    where
        GenIndex: Into<(I, G)>,
        I: Into<usize>,
    {
        let gen_index = gen_index.into();
        &mut self.inner.get_unchecked_mut(gen_index.0.into()).1
    }

    /// Returns the generation associated with the element at the index.
    ///
    /// Returns `None` if the index is out of bounds.
    #[inline]
    pub fn get_gen(&self, index: I) -> Option<&G>
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
        if elem.0 == generation {
            let prev_value = core::mem::replace(elem, (generation, value));
            Ok(prev_value)
        } else {
            assert!(
                generation < elem.0,
                "generation is greater than generation associated with element"
            );
            Err(Error::less_than_existing_generation())
        }
    }

    /// Sets a value at the given index if the generation is equal to the
    /// generation associated with the existing element.
    ///
    /// Returns the previous generation and the value for the element if successful.
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
    /// * if the generation is greater than the current generation associated
    /// with the element. To increase the generation, a call to
    /// [`set_gen`][UnmanagedGenVec::set_gen] must be called first.
    #[inline]
    pub fn set(&mut self, gen_index: GenIndex, value: T) -> Result<(G, T), Error>
    where
        GenIndex: Into<(I, G)>,
        G: PartialOrd,
        I: Into<usize>,
    {
        let gen_index = gen_index.into();
        self.internal_set(gen_index.0.into(), gen_index.1, value)
    }

    /// Sets or pushes the element at the index if the generation is equal to
    /// the existing generation associated with the element.
    ///
    /// Returns the previous generation and the value for the element if
    /// replacing an existing value.
    ///
    /// This method is a convenience method for the newest allocated
    /// generational index. Either the newest allocated generationl index is
    /// for an existing index or it is for the immediate next index if a
    /// value were to be pushed to the `Vec`.
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
    /// * if the generation is greater than the current generation associated
    /// with the element. To increase the generation, a call to
    /// [`set_gen`][UnmanagedGenVec::set_gen] must be called first.
    pub fn set_or_push(&mut self, gen_index: GenIndex, value: T) -> Result<Option<(G, T)>, Error>
    where
        GenIndex: Into<(I, G)>,
        G: PartialOrd,
        I: Into<usize>,
    {
        let (index, generation) = gen_index.into();
        let index = index.into();

        match index.cmp(&self.len()) {
            Ordering::Less => self.internal_set(index, generation, value).map(Some),
            Ordering::Equal => {
                debug_assert_eq!(index, self.len());
                self.push(generation, value);
                Ok(None)
            }
            Ordering::Greater => Err(Error::index_out_of_bounds()),
        }
    }

    /// Sets the generation for an index if the generation is one greater than
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
    ///
    /// # Panics
    ///
    /// Panics if the generation is not the next generation after the existing
    /// generation associated with the element.
    pub fn set_gen(&mut self, gen_index: GenIndex) -> Result<G, Error>
    where
        GenIndex: Into<(I, G)>,
        G: PartialOrd + Incrementable,
        I: Into<usize>,
    {
        let (index, generation) = gen_index.into();
        let elem = self
            .inner
            .get_mut(index.into())
            .ok_or_else(Error::index_out_of_bounds)?;
        if elem.0 < generation {
            assert!(
                elem.0.next().as_ref() == Some(&generation),
                "generation is not the next generation of the current element"
            );
            let prev_value = core::mem::replace(&mut elem.0, generation);
            Ok(prev_value)
        } else if elem.0 == generation {
            Err(Error::already_equal_generation())
        } else {
            Err(Error::less_than_existing_generation())
        }
    }
}

impl<T, G, I, GenIndex> core::ops::Index<GenIndex> for UnmanagedGenVec<T, G, I, GenIndex>
where
    I: Into<usize>,
    GenIndex: Into<(I, G)>,
    G: PartialEq,
{
    type Output = T;

    fn index(&self, gen_index: GenIndex) -> &Self::Output {
        let gen_index = gen_index.into();
        let idx = gen_index.0.into();
        let (cur_gen, elem) = &self.inner[idx];
        let expected_gen = gen_index.1;
        if expected_gen == *cur_gen {
            elem
        } else {
            panic!("generation is not equal");
        }
    }
}

impl<T, G, I, GenIndex> core::ops::IndexMut<GenIndex> for UnmanagedGenVec<T, G, I, GenIndex>
where
    I: Into<usize>,
    GenIndex: Into<(I, G)>,
    G: PartialEq,
{
    fn index_mut(&mut self, gen_index: GenIndex) -> &mut Self::Output {
        let gen_index = gen_index.into();
        let idx = gen_index.0.into();
        let (cur_gen, elem) = &mut self.inner[idx];
        let expected_gen = gen_index.1;
        if expected_gen == *cur_gen {
            elem
        } else {
            panic!("generation is not equal");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, PartialEq)]
    struct Value<T>(T);

    impl<T> Value<T> {
        fn set(&mut self, value: T) {
            self.0 = value;
        }
    }

    #[test]
    fn test_contains_index_out_of_bounds() {
        let gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        assert!(!gen_vec.contains_index((0, 0)));
    }

    #[test]
    fn test_contains_index_generation_less_than_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(1, Value(0));
        assert!(!gen_vec.contains_index((0, 0)));
    }

    #[test]
    fn test_contains_index_generation_greater_than_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(1, Value(0));
        assert!(!gen_vec.contains_index((2, 0)));
    }

    #[test]
    fn test_get_index_out_of_bounds() {
        let gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        let err = gen_vec.get((0, 0)).unwrap_err();
        assert!(err.is_index_out_of_bounds());
    }

    #[test]
    fn test_get_generation_less_than_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(1, Value(0));

        let err = gen_vec.get((0, 0)).unwrap_err();
        assert!(err.is_not_equal_generation_error());
    }

    #[test]
    fn test_get_generation_greater_than_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(1, Value(0));

        let err = gen_vec.get((0, 2)).unwrap_err();
        assert!(err.is_not_equal_generation_error());
    }

    #[test]
    fn test_get_mut_index_out_of_bounds() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        let err = gen_vec.get_mut((0, 0)).unwrap_err();
        assert!(err.is_index_out_of_bounds());
    }

    #[test]
    fn test_get_mut_generation_less_than_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(1, Value(0));

        let err = gen_vec.get_mut((0, 0)).unwrap_err();
        assert!(err.is_not_equal_generation_error());
    }

    #[test]
    fn test_get_mut_generation_greater_than_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(1, Value(0));

        let err = gen_vec.get_mut((0, 2)).unwrap_err();
        assert!(err.is_not_equal_generation_error());
    }

    #[test]
    fn test_get_gen_index_out_of_bounds() {
        let gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();

        assert_eq!(gen_vec.get_gen(0), None);
    }

    #[test]
    fn test_set_index_out_of_bounds() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        let err = gen_vec.set((0, 0), Value(1)).unwrap_err();
        assert!(err.is_index_out_of_bounds());
    }

    #[test]
    fn test_set_generation_less_than_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(1, Value(0));
        let err = gen_vec.set((0, 0), Value(1)).unwrap_err();
        assert!(err.is_generation_less_than_existing());
    }

    #[test]
    #[should_panic(expected = "generation is greater than generation associated with element")]
    fn test_set_generation_greater_than_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(0, Value(0));
        gen_vec.set((0, 1), Value(1)).unwrap();
    }

    #[test]
    fn test_set_or_push_index_out_of_bounds() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        let err = gen_vec.set_or_push((1, 0), Value(1)).unwrap_err();
        assert!(err.is_index_out_of_bounds());
    }

    #[test]
    fn test_set_or_push_generation_less_than_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(1, Value(0));
        let err = gen_vec.set((0, 0), Value(1)).unwrap_err();
        assert!(err.is_generation_less_than_existing());
    }

    #[test]
    #[should_panic(expected = "generation is greater than generation associated with element")]
    fn test_set_or_push_generation_greater_than_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(0, Value(0));
        gen_vec.set((0, 1), Value(1)).unwrap();
    }

    #[test]
    fn test_set_gen_index_out_of_bounds() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        let err = gen_vec.set_gen((0, 1)).unwrap_err();
        assert!(err.is_index_out_of_bounds());
    }

    #[test]
    fn test_set_gen_generation_already_equal() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(1, Value(0));
        let err = gen_vec.set_gen((0, 1)).unwrap_err();
        assert!(err.is_already_equal_generation_error());
    }

    #[test]
    fn test_set_gen_generation_less_than_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(2, Value(0));
        let err = gen_vec.set_gen((0, 1)).unwrap_err();
        assert!(err.is_generation_less_than_existing());
    }

    #[test]
    #[should_panic(expected = "generation is not the next generation of the current element")]
    fn test_set_gen_generation_greater_than_more_than_one_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(1, Value(0));
        let _ = gen_vec.set_gen((0, 3));
    }

    #[test]
    #[should_panic(expected = "index out of bounds")]
    fn test_index_out_of_bounds_index() {
        let gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        let _ = gen_vec[(0, 0)];
    }

    #[test]
    #[should_panic(expected = "generation is not equal")]
    fn test_index_generation_less_than_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(1, Value(0));
        let _ = &gen_vec[(0, 0)];
    }

    #[test]
    #[should_panic(expected = "generation is not equal")]
    fn test_index_generation_greater_than_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(0, Value(0));
        let _ = &gen_vec[(0, 1)];
    }

    #[test]
    #[should_panic(expected = "index out of bounds")]
    fn test_index_mut_out_of_bounds_index() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        let _ = &mut gen_vec[(0, 0)];
    }

    #[test]
    #[should_panic(expected = "generation is not equal")]
    fn test_index_mut_generation_less_than_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(1, Value(0));
        let _ = &mut gen_vec[(0, 0)];
    }

    #[test]
    #[should_panic(expected = "generation is not equal")]
    fn test_index_mut_generation_greater_than_existing() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();
        gen_vec.push(0, Value(0));
        let _ = &mut gen_vec[(0, 1)];
    }

    #[test]
    fn test_index_mut() {
        let mut gen_vec = UnmanagedGenVec::<Value<u32>, u8>::default();

        let index = gen_vec.len();
        assert_eq!(index, 0);
        let generation = 0;
        gen_vec.push(generation, Value(0));
        assert_eq!(gen_vec[(index, generation)], Value(0));

        let value = &mut gen_vec[(index, generation)];
        value.set(9);
        assert_eq!(gen_vec[(index, generation)], Value(9));
    }
}
