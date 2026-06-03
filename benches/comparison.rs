use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use obj_pool::ObjPool;
use slab::Slab;

const SIZES: &[usize] = &[100, 1_000, 10_000, 100_000];

// ---------------------------------------------------------------------------
// Insert
// ---------------------------------------------------------------------------

fn bench_insert(c: &mut Criterion) {
    let mut g = c.benchmark_group("insert");
    for &n in SIZES {
        g.bench_with_input(BenchmarkId::new("obj-pool", n), &n, |b, &n| {
            b.iter(|| {
                let mut pool = ObjPool::with_capacity(n);
                for i in 0..n {
                    pool.insert(i);
                }
                pool
            });
        });
        g.bench_with_input(BenchmarkId::new("slab", n), &n, |b, &n| {
            b.iter(|| {
                let mut slab = Slab::with_capacity(n);
                for i in 0..n {
                    slab.insert(i);
                }
                slab
            });
        });
    }
    g.finish();
}

// ---------------------------------------------------------------------------
// Get (sequential access)
// ---------------------------------------------------------------------------

fn bench_get(c: &mut Criterion) {
    let mut g = c.benchmark_group("get");
    for &n in SIZES {
        g.bench_with_input(BenchmarkId::new("obj-pool", n), &n, |b, &n| {
            let mut pool = ObjPool::with_capacity(n);
            let keys: Vec<_> = (0..n).map(|i| pool.insert(i)).collect();
            b.iter(|| {
                let mut sum = 0usize;
                for &k in &keys {
                    sum = sum.wrapping_add(*pool.get(k).unwrap());
                }
                sum
            });
        });
        g.bench_with_input(BenchmarkId::new("slab", n), &n, |b, &n| {
            let mut slab = Slab::with_capacity(n);
            let keys: Vec<_> = (0..n).map(|i| slab.insert(i)).collect();
            b.iter(|| {
                let mut sum = 0usize;
                for &k in &keys {
                    sum = sum.wrapping_add(slab[k]);
                }
                sum
            });
        });
    }
    g.finish();
}

// ---------------------------------------------------------------------------
// Remove + reinsert (slot reuse)
// ---------------------------------------------------------------------------

fn bench_remove_reinsert(c: &mut Criterion) {
    let mut g = c.benchmark_group("remove_reinsert");
    for &n in SIZES {
        g.bench_with_input(BenchmarkId::new("obj-pool", n), &n, |b, &n| {
            b.iter_batched(
                || {
                    let mut pool = ObjPool::with_capacity(n);
                    let keys: Vec<_> = (0..n).map(|i| pool.insert(i)).collect();
                    (pool, keys)
                },
                |(mut pool, keys)| {
                    // remove every other element then reinsert
                    for &k in keys.iter().step_by(2) {
                        pool.remove(k);
                    }
                    for i in 0..keys.len() / 2 {
                        pool.insert(i);
                    }
                    pool
                },
                BatchSize::LargeInput,
            );
        });
        g.bench_with_input(BenchmarkId::new("slab", n), &n, |b, &n| {
            b.iter_batched(
                || {
                    let mut slab = Slab::with_capacity(n);
                    let keys: Vec<_> = (0..n).map(|i| slab.insert(i)).collect();
                    (slab, keys)
                },
                |(mut slab, keys)| {
                    for &k in keys.iter().step_by(2) {
                        slab.remove(k);
                    }
                    for i in 0..keys.len() / 2 {
                        slab.insert(i);
                    }
                    slab
                },
                BatchSize::LargeInput,
            );
        });
    }
    g.finish();
}

// ---------------------------------------------------------------------------
// Iterate over occupied slots
// ---------------------------------------------------------------------------

fn bench_iter(c: &mut Criterion) {
    let mut g = c.benchmark_group("iter");
    for &n in SIZES {
        g.bench_with_input(BenchmarkId::new("obj-pool", n), &n, |b, &n| {
            let mut pool = ObjPool::with_capacity(n);
            for i in 0..n {
                pool.insert(i);
            }
            // remove every third to create gaps
            let keys: Vec<_> = pool.iter().map(|(k, _)| k).step_by(3).collect();
            for k in keys {
                pool.remove(k);
            }
            b.iter(|| {
                let mut sum = 0usize;
                for (_, &v) in pool.iter() {
                    sum = sum.wrapping_add(v);
                }
                sum
            });
        });
        g.bench_with_input(BenchmarkId::new("slab", n), &n, |b, &n| {
            let mut slab = Slab::with_capacity(n);
            for i in 0..n {
                slab.insert(i);
            }
            let keys: Vec<_> = slab.iter().map(|(k, _)| k).step_by(3).collect();
            for k in keys {
                slab.remove(k);
            }
            b.iter(|| {
                let mut sum = 0usize;
                for (_, &v) in slab.iter() {
                    sum = sum.wrapping_add(v);
                }
                sum
            });
        });
    }
    g.finish();
}

// ---------------------------------------------------------------------------
// Memory layout: key size and Option<Key> size
// ---------------------------------------------------------------------------

fn bench_memory(c: &mut Criterion) {
    let mut g = c.benchmark_group("memory_sizes");

    // This benchmark doesn't measure time — it prints sizes as throughput=bytes
    // so they show up in the report. Use n=1 so criterion runs it quickly.
    g.bench_function("ObjId size (bytes)", |b| {
        b.iter(|| std::hint::black_box(std::mem::size_of::<obj_pool::ObjId>()));
    });
    g.bench_function("Option<ObjId> size (bytes)", |b| {
        b.iter(|| std::hint::black_box(std::mem::size_of::<Option<obj_pool::ObjId>>()));
    });
    g.bench_function("slab key (usize) size (bytes)", |b| {
        b.iter(|| std::hint::black_box(std::mem::size_of::<usize>()));
    });
    g.bench_function("Option<usize> size (bytes)", |b| {
        b.iter(|| std::hint::black_box(std::mem::size_of::<Option<usize>>()));
    });

    g.finish();
}

criterion_group!(
    benches,
    bench_insert,
    bench_get,
    bench_remove_reinsert,
    bench_iter,
    bench_memory,
);
criterion_main!(benches);
