# obj-pool

[![crates.io](https://img.shields.io/crates/v/obj-pool.svg)](https://crates.io/crates/obj-pool)
[![docs.rs](https://docs.rs/obj-pool/badge.svg)](https://docs.rs/obj-pool)
[![License](https://img.shields.io/badge/license-Apache--2.0%2FMIT-blue.svg)](https://github.com/artemshein/obj-pool)

A typed object pool with compact 32-bit IDs, optional serde support, and a sharded parallel variant for concurrent workloads.

## Why obj-pool?

When building self-referential data structures (graphs, trees, linked lists) in Rust you have a few options:

1. Unsafe pointer manipulation.
2. `Rc<RefCell<T>>` — safe but verbose and allocation-heavy.
3. A plain `Vec<T>` with index-based access.

`ObjPool<T>` is a polished version of option 3. It handles slot reuse, provides a typed `ObjId` handle instead of a raw `usize`, and catches bugs in debug builds.

## Highlights

- **Compact IDs** — `ObjId` wraps `NonZeroU32`, so `Option<ObjId>` is 4 bytes with no extra space (niche optimization). A `slab` key is a full `usize` (8 bytes on 64-bit).
- **Debug-mode safety** — pools embed an offset into each `ObjId` in debug builds so accidental cross-pool access panics instead of silently returning wrong data.
- **Parallel pool** — `ParObjPool<T, S>` shards `S` inner pools behind `RwLock`s for concurrent insert/remove/lookup without a global lock.
- **Optional serde** — enable the `serde_support` feature to serialize/deserialize `ObjId` and pool contents.
- **`OptionObjId`** — a niche-optimized optional ID type backed by the `optional` crate.

## Usage

```toml
[dependencies]
obj-pool = "0.5"

# with serde:
obj-pool = { version = "0.5", features = ["serde_support"] }
```

### Single-threaded pool

```rust
use obj_pool::{ObjPool, ObjId};

let mut pool: ObjPool<String> = ObjPool::new();

let a: ObjId = pool.insert("hello".to_string());
let b: ObjId = pool.insert("world".to_string());

println!("{} {}", pool[a], pool[b]);

pool.remove(a);

// Slot `a` is reused for the next insert.
let c: ObjId = pool.insert("reused".to_string());
```

### Parallel pool

`ParObjPool<T, S>` distributes objects across `S` shards. `ObjId`s are self-contained — the shard index is encoded in the upper bits, so callers need no knowledge of the sharding.

```rust
use obj_pool::ParObjPool;
use std::sync::Arc;

let pool: Arc<ParObjPool<u64, 16>> = Arc::new(ParObjPool::new());

let id = pool.insert(42);

// Blocking read — returns a mapped read-guard.
assert_eq!(*pool.get(id).unwrap(), 42);

// Non-blocking — returns None if the shard lock is contended.
assert_eq!(pool.try_get(id).map(|v| *v), Some(42));
```

## ObjId vs usize

| | `obj-pool` `ObjId` | `slab` key |
|---|---|---|
| Width | 32-bit | 64-bit (usize) |
| `Option<K>` size | 4 bytes (niche) | 16 bytes |
| Cross-pool debug check | yes | no |
| Concurrent variant | `ParObjPool` | no |
| Serde | optional feature | no |

## License

Licensed under either of [Apache License 2.0](LICENSE-APACHE) or [MIT License](LICENSE-MIT) at your option.
