# GenValue

GenValue is a library for using values and indexes with a generation in a
`Vec`.

Generational indexes give a `Vec` an identifier which can always refer to the
same value (unless the value is removed) while re-using memory efficiently.

Generational indexes are commonly used in [entity component systems][wiki_ecs].

This library is a simple, naive, and general purpose implementation of the idea.
In most systems, an optimized and performant version of the idea (which depends on the
use case) can be built.

## Documentation

* [Latest API Docs][docs_rs_gen_value]

## Installation

```toml
[dependencies]
gen_value = "0.4.0"
```

## Examples

Using a `Vec` with generations associated with values and indexes.

```rust
use gen_value::{vec::GenVec, Error};

#[derive(Debug, PartialEq)]
struct Value<T>(T);

// The element type is `Value<u32>`.
// The generation type by default is a `u16`.
// The index type by default is a `usize`.
// The generational index type by default is a tuple `(usize, u16)`.
let mut gen_vec = GenVec::<Value<u32>>::default();

// Insert entities
let first_entity_index: (usize, u16) = gen_vec.insert(Value(42))?;
let other_entity_index = gen_vec.insert(Value(9))?;
assert_eq!(gen_vec.get(first_entity_index).ok(), Some(&Value(42)));
assert_eq!(*gen_vec.get(other_entity_index)?, Value(9));
assert_eq!(gen_vec.len(), 2);

// Remove first entity's value
gen_vec.remove(first_entity_index)?;

// Other entity can still be retrieved with same index 
assert_eq!(*gen_vec.get(other_entity_index)?, Value(9));
// Cannot get first entity's value
assert_eq!(gen_vec.get(first_entity_index).ok(), None);
// `Vec` length is still 2
assert_eq!(gen_vec.len(), 2);

// Insert last entity
let last_entity_index = gen_vec.insert(Value(3))?;
assert_eq!(*gen_vec.get(other_entity_index)?, Value(9));
assert_eq!(*gen_vec.get(last_entity_index)?, Value(3));
// First entity index still cannot access a value
assert!(gen_vec.get(first_entity_index).is_err());
assert_eq!(gen_vec.len(), 2);

// The indexes and generations used
assert_eq!(first_entity_index, (0, 0));
assert_eq!(other_entity_index, (1, 0));
// The last entity re-used index 0 but with a newer generation
assert_eq!(last_entity_index, (0, 1));

Ok::<_, Error>(())
```

## Motivation

It is relatively fast to access an element in a `Vec`. Given an index, a
relatively simple offset calculation is made from the beginning of the vector and
an element can be read. Even better, because a vector's elements are located
adjacent in memory, vectors are ideal for CPU cache prefetching.

In comparision, a `HashMap` requires hashing a key and then possibly following
multiple pointers to find the element. A `BTreeMap` may have to do several
comparisions before finding the entry with the desired key. Both should be
relatively slower than accessing an element by an index in a `Vec`.

On the other hand, a `Vec` index is not usually a stable identifier for an
element. By inserting a new element or removing an element, the positions for
the elements usually change, so an index may access different elements over
time.

For a `HashMap` and a `BTreeMap`, keys are stable identifiers for
values (as long as the keys follow the documented invariants). If a key is used
to store a value in a map, an equal key can be used to retrieve the value later
(assuming the value was not removed). The keys can be copied to various parts of
the program and still be used later.

In many use cases, mapping stable identifiers to values is desirable.

How can we have stable identifiers and yet try to keep the performance
properties for a `Vec`?

### Never Move Elements

One way for a `Vec` to have stable identifiers is to never move elements. Once a
value is pushed to the end of the `Vec`, the value will always have the same
index. All operations which move elements can be disallowed (e.g. inserting a
new element at a position).

Still, removing an element from a collection is important functionality. A
possible solution is to add a "removed" tombstone value by using a
`Vec<Option<T>>`. Values are pushed as `Some(T)` and when removed will be set to
`None`. Indexes become stable identifiers for elements.

Unfortunately, there is an increasing amount of unused memory as elements are
set to `None` when being removed.

### Indexes and Values with Generations

Generational indexes are a possible solution to maximizing the usage of memory
while keeping elements in the same position. Every element in the `Vec` is
associated with a generation value, which is usually an integer. A generational
index is an index with a generation value. Depending on if the generation values
match or if one generation value is greater than another, an operation will
succeed.

> A `Vec<T>` becomes `Vec<(G, T)>` and an individual element index `I` becomes
> `(I, G)` where `G` is the generation type.

So in a `Vec<(usize, Person)>`, the element at index `9` could have `2` for the
generation and a `Person` value. If the generational index `(9, 2)` is used, the
element at the 9th offset is read. Then, the generation associated with the
`Person` value is compared with the generation associated with the index. Since
both are `2`, the operation succeeds. If the generational index was `(9, 1)`,
then the operation would fail because the generations would not match.

Suppose there is a generational index (`(3,1)`) and the `Vec` at index `3` has a
value with generation `1`. When the element is "removed", the generation
associated with the value in the `Vec` is increased. So the `Vec` would have
generation `2` at index `3`. The generational index (`(3,1)`) could no longer be
used to access the `Vec` value at index `3` because the generations are no
longer equal. While the value is not technically dropped (in Rust's
terminology), the value is effectively removed from access.

The index with the latest generation is available to store a new value, so
memory is reused instead of left unused. An entity using the previous generation
of an index will no longer be able to access the removed value while an entity
using the latest generation of the index will retrieve the value at the index.

The allocation of new indexes and increases in generations must be logically
correct for program correctness.

## Similar Projects

* [generational-arena][generational_arena]
* [gen-vec][gen_vec]

Both crates are inspired by [Catherine West's excellent closing keynote for
RustConf 2018][rustconf_2018_closing_keynote].

The major difference between the other crates is this crate's direct control of
the index types and generation types through type parameters. If a use case only
needs the generation to be `u8`, this crate can use a `u8`. The generational
index type itself can be specified (instead of using a single `Index` type or
`(I, G)` tuple) for some type safety use cases. Each crate chose different APIs
to expose.

## License

Licensed under either of [Apache License, Version 2.0][LICENSE_APACHE] or [MIT
License][LICENSE_MIT] at your option.

### Contributions

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[LICENSE_APACHE]: LICENSE-APACHE
[LICENSE_MIT]: LICENSE-MIT
[wiki_ecs]: https://en.wikipedia.org/wiki/Entity_component_system
[docs_rs_gen_value]: https://docs.rs/gen_value/
[BTreeMap]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
[Vec]: https://doc.rust-lang.org/std/vec/struct.Vec.html
[generational_arena]: https://crates.io/crates/generational-arena
[gen_vec]: https://crates.io/crates/gen-vec
[rustconf_2018_closing_keynote]: https://www.youtube.com/watch?v=aKLntZcp27M 