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
