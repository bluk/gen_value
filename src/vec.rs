// Copyright 2022 Bryant Luk
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! `Vec` indexed with internally managed generational indexes.
//!
//! Every value in the vector has a generation associated with it. When
//! accessing elements from the `GenVec`, an index with a generation is required. The
//! generational index is composed of an index (like a [usize]) and a generation
//! (usually an unsigned integer).
//!
//! The index is used exactly like an individual element index in a `Vec`.
//! However, before accessing the value, the generation associated with the
//! element is checked to determine if the operation should proceed.
//!
//! To get an element, the generations must be equal. To set an element, the
//! generation must be equal to or greater than the existing generation. The
//! element is set with the latest generation.
//!
//! When removing an element, the generation must be equal to or greater than
//! the existing generation. The generation associated with the element is
//! incremented but the value is not dropped from the vector. The value is only
//! dropped when another value is set at the index.
//!
//! # Design Considerations
//!
//! ## Benefits
//!
//! * Generational indexes can be stored by other parts of the program and
//! guaranteed to always reference the same value (until it is removed)
//! * The underlying Vec will not need to move elements when elements are removed
//! * Once an element is removed by increasing the generation at the index,
//! existing generational indexes for the index will be effectively invalidated
//! (because the stored indexes do not have the correct generation)
//! * Access is still relatively fast
//! * Memory is reused when possible (by re-using an index in a [`Vec`])
//!
//! ## Drawbacks
//!
//! * Values are not dropped until a new value is set for the index
//! * The `GenVec` does not reclaim unused memory. While the `GenVec` can re-use
//! indexes with increases in the generation, the length will be equal to at
//! least the largest number of concurrently active elements during a program's
//! execution. If there are 200 concurrent active entities, then the
//! `GenVec` will always have at least a length of 200 for the remainder of the
//! program's execution.
//! * Note that the limit for the maximum number of concurrently active elements
//! can decrease over time. Initially, the maximum number is equivalent to the
//! maximum number of elements possible in a [`Vec`] (a [usize]). If a single
//! index is reused through all of the generational cycles, then the index can
//! no longer be used, so the limit for the maximum number of concurrently active
//! elements decreases. If a generation is represented with a [u8], imagine 256
//! active entities but only 1 entity is ever active at a time. All
//! of the generations would be exhausted at index `0`, so after that point,
//! `usize::MAX` - `1` is the theoretical maximum number of concurrently active
//! elements (actually only `isize::MAX` - 1 due to the limits of `Vec`).
//! The memory for index `0` is essentially leaked at that point.
//! * There is a limit to the total number of elements that can ever be stored
//! by the `GenVec`. If a generation is represented with a [u8], then there are
//! 256 generations per index. Assume that all indexes can eventually be used
//! and indexes are represented by a [u32]. Then, 2^8 * 2^32 (2^40) total
//! elements can ever be stored.
//!
//! The limits are important to keep in mind, but in practice, with a sufficient
//! sized index and generation type, the limits will never be encounted.

use crate::{index::Allocator, unmanaged::UnmanagedGenVec, Error, Incrementable};

/// `Vec` indexed with generational indexes.
///
/// `GenVec` manages its own generational indexes and allocates and deallocates
/// indexes appropriately. Indexes constructed or allocated by external sources
/// should not be used.
///
/// If a single `Vec` with generational indexes is required, then using `GenVec`
/// is useful. If generational indexes must be allocated and deallocated
/// externally or if multiple vectors are required, then the [`Allocator`] and
/// [`UnmanagedGenVec`] may be more useful.
///
/// Generational indexes are allocated on [`GenVec::insert()`] and are deallocated
/// with [`GenVec::remove()`].
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
/// ## I
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
/// ## Index
///
/// `Index` is the type which the generational index should be returned as. A tuple
/// like `(I, G)` can be used or a custom type. By default, `(I, G)` is used.
///
/// The generational index type is generally treated like an opaque identifier.
/// While a tuple is useful, a custom type may be desired so a generational
/// index is only used with collections which take the custom type.
///
/// `Index` types must implement:
///
/// * `From<(I, G)> for Index`
/// * `Into<(I, G)> for Index`
#[derive(Debug)]
#[allow(clippy::module_name_repetitions)]
pub struct GenVec<T, G = u16, I = usize, Index = (I, G)> {
    allocator: Allocator<G, I, Index>,
    inner: UnmanagedGenVec<T, G>,
}

impl<T, G, I, Index> GenVec<T, G, I, Index> {
    /// Constructs a new inner [`Vec`].
    ///
    /// See [`Vec::new`] for additional information.
    #[must_use]
    pub fn new() -> Self
    where
        I: Default,
    {
        Self {
            allocator: Allocator::new(),
            inner: UnmanagedGenVec::new(),
        }
    }

    /// Constructs an inner [`Vec`] with the given capacity.
    ///
    /// See [`Vec::with_capacity`] for additional information.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self
    where
        I: Default,
    {
        Self {
            allocator: Allocator::new(),
            inner: UnmanagedGenVec::with_capacity(capacity),
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

impl<T, G, I, Index> Default for GenVec<T, G, I, Index>
where
    I: Default,
{
    fn default() -> Self {
        Self {
            allocator: Allocator::default(),
            inner: UnmanagedGenVec::default(),
        }
    }
}

impl<T, G, I, Index> GenVec<T, G, I, Index>
where
    I: Into<usize>,
{
    /// Inserts a new value into the collection.
    ///
    /// The index of the value may be at any position in the underlying [`Vec`].
    /// If there are no available positions, then the new value may be pushed
    /// onto the end of the [`Vec`].
    ///
    /// On success, the generational index of the element is returned.
    ///
    /// # Errors
    ///
    /// Errors are returned if:
    ///
    /// * a generational index cannot be created
    pub fn insert(&mut self, value: T) -> Result<Index, Error>
    where
        Index: From<(I, G)> + Into<(I, G)>,
        G: Clone + Default + PartialOrd,
        I: Clone + Incrementable,
    {
        let gen_index = self
            .allocator
            .alloc()
            .ok_or_else(Error::cannot_allocate_generational_index)?;
        let (index, generation) = gen_index.into();
        self.inner
            .set_or_push((index.clone(), generation.clone()), value)
            .expect("set of push should have succeeded");
        Ok(Index::from((index, generation)))
    }

    /// Returns true if an element exists for the generational index.
    #[must_use]
    pub fn contains_index(&self, gen_index: Index) -> bool
    where
        Index: Into<(I, G)>,
        G: PartialEq,
    {
        self.inner.get(gen_index.into()).is_ok()
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
    pub fn get(&self, gen_index: Index) -> Result<&T, Error>
    where
        Index: Into<(I, G)>,
        G: PartialEq,
    {
        self.inner.get(gen_index.into())
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
    pub fn get_mut(&mut self, gen_index: Index) -> Result<&mut T, Error>
    where
        Index: Into<(I, G)>,
        G: PartialEq,
    {
        self.inner.get_mut(gen_index.into())
    }

    /// Returns a reference to the element at the given index.
    ///
    /// See [`slice::get_unchecked`] for additional information.
    ///
    /// # Safety
    ///
    /// There is no bounds check and no generation check performed. If the index is out of bounds, undefined behavior will occur.
    pub unsafe fn get_unchecked(&self, gen_index: Index) -> &T
    where
        Index: Into<(I, G)>,
    {
        self.inner.get_unchecked(gen_index.into())
    }

    /// Returns a mutable reference to the element at the given index.
    ///
    /// See [`slice::get_unchecked_mut`] for additional information.
    ///
    /// # Safety
    ///
    /// There is no bounds check and no generation check performed. If the index is out of bounds, undefined behavior will occur.
    pub unsafe fn get_unchecked_mut(&mut self, gen_index: Index) -> &mut T
    where
        Index: Into<(I, G)>,
    {
        self.inner.get_unchecked_mut(gen_index.into())
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
    pub fn set(&mut self, gen_index: Index, value: T) -> Result<(G, T), Error>
    where
        Index: Into<(I, G)>,
        G: PartialOrd,
    {
        self.inner.set(gen_index.into(), value)
    }

    /// Removes access to an element which matches the generation of the element.
    ///
    /// # Important
    ///
    /// If the generation is the last generation (the maximum generation value),
    /// then the value will remain accessible for any generational index with
    /// the same index and last generation.
    ///
    /// # Errors
    ///
    /// Errors are returned if:
    ///
    /// * the index is out of bounds
    pub fn remove(&mut self, gen_index: Index) -> Result<(), Error>
    where
        Index: From<(I, G)> + Into<(I, G)>,
        G: Clone + PartialOrd + Incrementable,
        I: Clone,
    {
        let (index, generation) = gen_index.into();
        if let Some(next_gen) = generation.next() {
            match self.inner.set_gen((index.clone(), next_gen)) {
                Ok(_prev_gen) => {
                    self.allocator.dealloc(Index::from((index, generation)));
                }
                Err(error) if error.is_already_equal_generation_error() => {}
                Err(error) => return Err(error),
            }
        }
        Ok(())
    }
}

impl<T, G, I, Index> core::ops::Index<Index> for GenVec<T, G, I, Index>
where
    Index: Into<(I, G)>,
    I: Into<usize>,
    G: PartialEq,
{
    type Output = T;

    fn index(&self, gen_index: Index) -> &Self::Output {
        let (index, generation) = gen_index.into();
        &self.inner[(index, generation)]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, PartialEq)]
    struct Value<T> {
        inner: T,
    }

    impl<T> Value<T> {
        fn new(inner: T) -> Self {
            Self { inner }
        }

        fn set(&mut self, value: T) {
            self.inner = value;
        }
    }

    #[test]
    fn test_usage() -> Result<(), Error> {
        let mut gen_vec = GenVec::<Value<u32>, u32, usize, (usize, u32)>::default();

        assert_eq!(gen_vec.len(), 0);
        assert!(gen_vec.is_empty());

        // Insert first entity
        let first_entity_index = gen_vec.insert(Value::new(42))?;
        assert_eq!(*gen_vec.get(first_entity_index)?, Value::new(42));
        assert!(gen_vec.contains_index(first_entity_index));
        assert_eq!(gen_vec.len(), 1);
        assert!(!gen_vec.is_empty());

        // Change first entity's value
        let first_entity_value = gen_vec.get_mut(first_entity_index)?;
        first_entity_value.set(1001);
        assert_eq!(*gen_vec.get(first_entity_index)?, Value::new(1001));
        // Turn Result into Option with ok()
        assert_eq!(
            gen_vec.get(first_entity_index).ok(),
            Some(&Value::new(1001))
        );
        assert_eq!(gen_vec.len(), 1);

        // Set first entity's value
        let set_first_entity_result = gen_vec.set(first_entity_index, Value::new(1002))?;
        assert_eq!(set_first_entity_result, (0, Value::new(1001)));
        assert_eq!(*gen_vec.get(first_entity_index)?, Value::new(1002));
        assert_eq!(gen_vec.len(), 1);

        // Insert other entity value
        let other_entity_index = gen_vec.insert(Value::new(9))?;
        assert_eq!(*gen_vec.get(first_entity_index)?, Value::new(1002));
        assert_eq!(*gen_vec.get(other_entity_index)?, Value::new(9));
        assert_eq!(gen_vec.len(), 2);

        // Remove first entity's value
        gen_vec.remove(first_entity_index)?;
        assert!(!gen_vec.contains_index(first_entity_index));

        // Cannot get first entity's value
        {
            let get_first_entity_result = gen_vec.get(first_entity_index);
            assert!(get_first_entity_result.is_err());
            assert!(get_first_entity_result
                .unwrap_err()
                .is_not_equal_generation_error());
        }

        // Cannot set first entity's value
        {
            let set_first_entity_result = gen_vec.set(first_entity_index, Value::new(1002));
            assert!(set_first_entity_result.is_err());
            assert!(set_first_entity_result
                .unwrap_err()
                .is_generation_less_than_existing());
        }

        // Other entity can still be retrieved with same index and length is still 2
        assert_eq!(*gen_vec.get(other_entity_index)?, Value::new(9));
        assert_eq!(gen_vec.len(), 2);

        // Insert last entity
        let last_entity_index = gen_vec.insert(Value::new(3))?;
        assert_eq!(*gen_vec.get(other_entity_index)?, Value::new(9));
        assert_eq!(*gen_vec.get(last_entity_index)?, Value::new(3));
        assert_eq!(gen_vec.len(), 2);

        assert!(gen_vec.get(first_entity_index).is_err());

        assert_eq!(first_entity_index, (0, 0));
        assert_eq!(other_entity_index, (1, 0));
        assert_eq!(last_entity_index, (0, 1));

        Ok::<_, Error>(())
    }

    #[test]
    fn test_exhaust_single_index() -> Result<(), Error> {
        let mut gen_vec = GenVec::<Value<u32>, u8>::default();

        let mut gen_index = (0, 0);
        for i in 0..=u8::MAX {
            gen_index = gen_vec.insert(Value::new(u32::from(i)))?;
            assert_eq!((0, i), gen_index);
            gen_vec.remove(gen_index)?;
        }

        assert_eq!(gen_vec.len(), 1);
        assert!(!gen_vec.is_empty());

        let new_gen_index = gen_vec.insert(Value::new(256))?;
        assert_eq!((1, 0), new_gen_index);

        // Attempt to remove old index again
        assert_eq!((0, 255), gen_index);
        gen_vec.remove(gen_index)?;

        let new_gen_index = gen_vec.insert(Value::new(257))?;
        assert_eq!((2, 0), new_gen_index);

        Ok::<_, Error>(())
    }

    #[test]
    fn test_remove_old_index_repeatedly() -> Result<(), Error> {
        let mut gen_vec = GenVec::<Value<u32>, u8>::default();

        let gen_index = gen_vec.insert(Value::new(0))?;
        assert_eq!(gen_index, (0, 0));
        gen_vec.remove(gen_index)?;

        // Remove old generation index again
        gen_vec.remove(gen_index)?;

        let newer_gen_index = gen_vec.insert(Value::new(1))?;
        assert_eq!(newer_gen_index, (0, 1));
        assert_eq!(gen_vec.len(), 1);

        // Remove old generation index again
        gen_vec.remove(gen_index)?;

        let newer_gen_index = gen_vec.insert(Value::new(2))?;
        assert_eq!(newer_gen_index, (1, 0));
        assert_eq!(gen_vec.len(), 2);

        Ok::<_, Error>(())
    }
}
