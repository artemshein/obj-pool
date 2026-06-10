0.7.0
=====

* **Breaking:** `ObjPool::obj_id_to_index` and `ObjPool::index_to_obj_id` are instance methods
  now, and the redundant static conversion helpers on `Iter`, `IterMut`, and `IntoIter` are
  removed.
* **Breaking:** `ObjPool::clear` now releases the allocated memory instead of keeping it for
  reuse (`ParObjPool::clear` already did).
* Debug builds now mix a random pool-specific offset into every `ObjId`, so an id used with a
  pool other than the one that created it is rejected instead of silently aliasing an unrelated
  object. Release builds are unaffected.
* `ParObjPool` derives the shard/index bit split of external ids from the shard count `S`
  instead of hardcoding 6 shard bits: each shard can now hold up to `2^(32 - ceil(log2(S))) - 1`
  objects, any `S` from 1 to 2^31 works, and invalid shard counts fail at compile time.
* `ParObjPool` lookups now return `None` for ids decoding to a nonexistent shard instead of
  panicking.
* Replace the unmaintained `unreachable` dependency with `std::hint::unreachable_unchecked`.
* Re-enable the linked-list and splay-tree examples, ported to the current API.
* Require parking_lot 0.12.5, use the `Apache-2.0 OR MIT` SPDX license expression.

0.6.0
=====

* Upgrade to Rust edition 2024.
* Add `size_hint`, `ExactSizeIterator`, and `FusedIterator` to `Iter`, `IterMut`, and `IntoIter`.
* Fix 2× iteration slowdown vs `slab`: `ObjId::from_index` now uses `new_unchecked` in release builds, allowing the compiler to eliminate key construction when the result is discarded.
* Add GitHub Actions CI (test on stable/beta/nightly, clippy, rustfmt).
* Add criterion benchmarks comparing `obj-pool` vs `slab`.
* Rewrite README with usage examples and benchmark data.

0.5.1
=====

* Added try_get and try_get_mut for ParObjPool

0.5.0
=====

* Shared implementation ParObjPool

0.4.4
=====

* Add ObjPool::new_const 

0.4.2
=====

* Enable serde support for optional

0.4.1
=====

* Add serde_support feature

0.4.0
=====

* Make ObjId field public for static usage
* Update dependencies

0.3.1
=====

* Fixed release build issue.

0.3.0
=====

* Switched to `optional` crate, remove invalid_value module.

0.2.0
=====

* Added debug-only check that `ObjId` used to get object from `ObjPool` is got from the correct `ObjPool`.
* Reintroduced iterators.
* Added `OptionObjId`.

0.1.0
=====

Initial version.
* Undeprecated `vec-arena`.
* Added `ObjId`.
