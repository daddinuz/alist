use std::collections::{BTreeMap, HashMap};
use std::hash::Hash;
use std::hint::black_box;

use alist::{AList, FastEq};
use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};

const SIZES: [usize; 4] = [8, 16, 32, 64];
const MIXED_USAGE_ROUNDS: usize = 32;

enum MixedOperation {
    Insert(isize, String),
    Remove(isize),
    Get(isize),
}

fn checksum(value: &str) -> usize {
    value
        .as_bytes()
        .iter()
        .fold(value.len(), |sum, byte| sum.wrapping_add(*byte as usize))
}

fn key(index: usize) -> isize {
    index as isize * 13 * if index & 1 == 0 { 1 } else { -1 }
}

fn random_indices(start: usize, count: usize, stride: usize) -> impl Iterator<Item = usize> {
    (0..count).map(move |index| start + index * stride % count)
}

fn entries(size: usize) -> Vec<(isize, String)> {
    random_indices(0, size, 5)
        .map(|index| (key(index), format!("{index} value")))
        .collect()
}

fn additional_entries(size: usize) -> Vec<(isize, String)> {
    random_indices(size, size, 3)
        .map(|index| (key(index), format!("{index} value")))
        .collect()
}

fn existing_keys(size: usize) -> Vec<isize> {
    random_indices(0, size, 7).map(key).collect()
}

fn missing_keys(size: usize) -> Vec<isize> {
    random_indices(size, size, 11).map(key).collect()
}

fn mixed_operations(size: usize) -> Vec<MixedOperation> {
    let mut present_keys = random_indices(0, size, 5).map(key).collect::<Vec<_>>();
    let mut missing_keys = random_indices(size, size.max(MIXED_USAGE_ROUNDS), 7)
        .map(key)
        .collect::<Vec<_>>();

    let mut operations = Vec::with_capacity(MIXED_USAGE_ROUNDS * 4);

    for round in 0..MIXED_USAGE_ROUNDS {
        operations.push(MixedOperation::Get(
            present_keys[(round * 7 + 3) % present_keys.len()],
        ));

        let removed_key = present_keys.swap_remove((round * 11 + 5) % present_keys.len());
        operations.push(MixedOperation::Remove(removed_key));

        let inserted_key = missing_keys.swap_remove((round * 13 + 7) % missing_keys.len());
        operations.push(MixedOperation::Get(inserted_key));
        operations.push(MixedOperation::Insert(
            inserted_key,
            format!("mixed {round} value"),
        ));

        present_keys.push(inserted_key);
        missing_keys.push(removed_key);
    }

    operations
}

fn map_default<M: Map<isize, String>>(entries: &[(isize, String)]) -> M {
    let mut map = M::default();
    map.extend(entries.iter().cloned());
    map
}

fn map_with_capacity<M: Map<isize, String>>(entries: &[(isize, String)]) -> M {
    let mut map = M::with_capacity(entries.len());
    map.extend(entries.iter().cloned());
    map
}

fn scenario_map_default<M: Map<isize, String>>(entries: &[(isize, String)]) -> usize {
    black_box(map_default::<M>(black_box(entries))).len()
}

fn scenario_map_with_capacity<M: Map<isize, String>>(entries: &[(isize, String)]) -> usize {
    black_box(map_with_capacity::<M>(black_box(entries))).len()
}

fn scenario_get_existing<M: Map<isize, String>>(map: &M, keys: &[isize]) -> usize {
    let mut sum = 0;
    for key in keys {
        sum += black_box(map.get(black_box(key)))
            .map(|value| checksum(black_box(value)))
            .unwrap_or_default();
    }
    sum
}

fn scenario_get_missing<M: Map<isize, String>>(map: &M, keys: &[isize]) -> usize {
    let mut misses = 0;
    for key in keys {
        misses += usize::from(black_box(map.get(black_box(key))).is_none());
    }
    misses
}

fn scenario_insert<M: Map<isize, String>>(map: &mut M, entries: &[(isize, String)]) -> usize {
    for (key, value) in entries {
        black_box(map.insert(black_box(*key), black_box(value.clone())));
    }
    map.len()
}

fn scenario_remove<M: Map<isize, String>>(map: &mut M, keys: &[isize]) -> usize {
    let mut removed = 0;
    for key in keys {
        removed += usize::from(black_box(map.remove(black_box(key))).is_some());
    }
    removed
}

fn scenario_mixed_usage<M: Map<isize, String>>(mut map: M, operations: &[MixedOperation]) -> usize {
    let mut observed = 0usize;

    for operation in operations {
        match operation {
            MixedOperation::Insert(key, value) => {
                if let Some(value) =
                    black_box(map.insert(black_box(*key), black_box(value.clone())))
                {
                    observed = observed.wrapping_add(checksum(black_box(&value)));
                }
            }
            MixedOperation::Remove(key) => {
                if let Some(value) = black_box(map.remove(black_box(key))) {
                    observed = observed.wrapping_add(checksum(black_box(&value)));
                }
            }
            MixedOperation::Get(key) => {
                observed = observed.wrapping_add(
                    black_box(map.get(black_box(key)))
                        .map(|value| checksum(black_box(value)))
                        .unwrap_or_default(),
                );
            }
        }
    }

    observed.wrapping_add(map.len())
}

fn scenario_iter<M: Map<isize, String>>(map: &M) -> usize {
    map.iter()
        .map(|(key, value)| black_box(*key as usize).wrapping_add(checksum(black_box(value))))
        .fold(0, usize::wrapping_add)
}

fn bench_default(c: &mut Criterion) {
    let mut group = c.benchmark_group("map/default");

    for size in SIZES {
        let entries = entries(size);
        group.throughput(Throughput::Elements(size as u64));

        group.bench_with_input(BenchmarkId::new("AList", size), &entries, |b, entries| {
            b.iter(|| black_box(scenario_map_default::<AList<_, _>>(entries)));
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &entries, |b, entries| {
            b.iter(|| black_box(scenario_map_default::<HashMap<_, _>>(entries)));
        });
        group.bench_with_input(
            BenchmarkId::new("BTreeMap", size),
            &entries,
            |b, entries| {
                b.iter(|| black_box(scenario_map_default::<BTreeMap<_, _>>(entries)));
            },
        );
    }

    group.finish();
}

fn bench_with_capacity(c: &mut Criterion) {
    let mut group = c.benchmark_group("map/with_capacity");

    for size in SIZES {
        let entries = entries(size);
        group.throughput(Throughput::Elements(size as u64));

        group.bench_with_input(BenchmarkId::new("AList", size), &entries, |b, entries| {
            b.iter(|| black_box(scenario_map_with_capacity::<AList<_, _>>(entries)));
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &entries, |b, entries| {
            b.iter(|| black_box(scenario_map_with_capacity::<HashMap<_, _>>(entries)));
        });
        group.bench_with_input(
            BenchmarkId::new("BTreeMap", size),
            &entries,
            |b, entries| {
                b.iter(|| black_box(scenario_map_with_capacity::<BTreeMap<_, _>>(entries)));
            },
        );
    }

    group.finish();
}

fn bench_get_existing(c: &mut Criterion) {
    let mut group = c.benchmark_group("map/get_existing");

    for size in SIZES {
        let entries = entries(size);
        let keys = existing_keys(size);

        let alist = map_with_capacity::<AList<_, _>>(&entries);
        let hash_map = map_with_capacity::<HashMap<_, _>>(&entries);
        let btree_map = map_with_capacity::<BTreeMap<_, _>>(&entries);

        group.throughput(Throughput::Elements(size as u64));

        group.bench_with_input(BenchmarkId::new("AList", size), &keys, |b, keys| {
            b.iter(|| black_box(scenario_get_existing(&alist, keys)));
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &keys, |b, keys| {
            b.iter(|| black_box(scenario_get_existing(&hash_map, keys)));
        });
        group.bench_with_input(BenchmarkId::new("BTreeMap", size), &keys, |b, keys| {
            b.iter(|| black_box(scenario_get_existing(&btree_map, keys)));
        });
    }

    group.finish();
}

fn bench_get_missing(c: &mut Criterion) {
    let mut group = c.benchmark_group("map/get_missing");

    for size in SIZES {
        let entries = entries(size);
        let keys = missing_keys(size);

        let alist = map_with_capacity::<AList<_, _>>(&entries);
        let hash_map = map_with_capacity::<HashMap<_, _>>(&entries);
        let btree_map = map_with_capacity::<BTreeMap<_, _>>(&entries);

        group.throughput(Throughput::Elements(size as u64));

        group.bench_with_input(BenchmarkId::new("AList", size), &keys, |b, keys| {
            b.iter(|| black_box(scenario_get_missing(&alist, keys)));
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &keys, |b, keys| {
            b.iter(|| black_box(scenario_get_missing(&hash_map, keys)));
        });
        group.bench_with_input(BenchmarkId::new("BTreeMap", size), &keys, |b, keys| {
            b.iter(|| black_box(scenario_get_missing(&btree_map, keys)));
        });
    }

    group.finish();
}

fn bench_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("map/insert");

    for size in SIZES {
        let entries = entries(size);
        let insertions = additional_entries(size);
        group.throughput(Throughput::Elements(size as u64));

        group.bench_with_input(
            BenchmarkId::new("AList", size),
            &insertions,
            |b, insertions| {
                b.iter_batched(
                    || map_with_capacity::<AList<_, _>>(&entries),
                    |mut map| black_box(scenario_insert(&mut map, insertions)),
                    BatchSize::SmallInput,
                );
            },
        );
        group.bench_with_input(
            BenchmarkId::new("HashMap", size),
            &insertions,
            |b, insertions| {
                b.iter_batched(
                    || map_with_capacity::<HashMap<_, _>>(&entries),
                    |mut map| black_box(scenario_insert(&mut map, insertions)),
                    BatchSize::SmallInput,
                );
            },
        );
        group.bench_with_input(
            BenchmarkId::new("BTreeMap", size),
            &insertions,
            |b, insertions| {
                b.iter_batched(
                    || map_with_capacity::<BTreeMap<_, _>>(&entries),
                    |mut map| black_box(scenario_insert(&mut map, insertions)),
                    BatchSize::SmallInput,
                );
            },
        );
    }

    group.finish();
}

fn bench_remove(c: &mut Criterion) {
    let mut group = c.benchmark_group("map/remove");

    for size in SIZES {
        let entries = entries(size);
        let keys = existing_keys(size);
        group.throughput(Throughput::Elements(size as u64));

        group.bench_with_input(BenchmarkId::new("AList", size), &keys, |b, keys| {
            b.iter_batched(
                || map_with_capacity::<AList<_, _>>(&entries),
                |mut map| black_box(scenario_remove(&mut map, keys)),
                BatchSize::SmallInput,
            );
        });
        group.bench_with_input(BenchmarkId::new("HashMap", size), &keys, |b, keys| {
            b.iter_batched(
                || map_with_capacity::<HashMap<_, _>>(&entries),
                |mut map| black_box(scenario_remove(&mut map, keys)),
                BatchSize::SmallInput,
            );
        });
        group.bench_with_input(BenchmarkId::new("BTreeMap", size), &keys, |b, keys| {
            b.iter_batched(
                || map_with_capacity::<BTreeMap<_, _>>(&entries),
                |mut map| black_box(scenario_remove(&mut map, keys)),
                BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

fn bench_mixed_usage(c: &mut Criterion) {
    let mut group = c.benchmark_group("map/mixed_usage");

    for size in SIZES {
        let entries = entries(size);
        let operations = mixed_operations(size);

        // Leave throughput unset: Criterion uses throughput as the line-chart x-axis,
        // and this scenario keeps the operation count fixed while varying map size.
        group.bench_with_input(
            BenchmarkId::new("AList", size),
            &operations,
            |b, operations| {
                b.iter_batched(
                    || map_with_capacity::<AList<_, _>>(&entries),
                    |map| black_box(scenario_mixed_usage(map, black_box(operations.as_slice()))),
                    BatchSize::SmallInput,
                );
            },
        );
        group.bench_with_input(
            BenchmarkId::new("HashMap", size),
            &operations,
            |b, operations| {
                b.iter_batched(
                    || map_with_capacity::<HashMap<_, _>>(&entries),
                    |map| black_box(scenario_mixed_usage(map, black_box(operations.as_slice()))),
                    BatchSize::SmallInput,
                );
            },
        );
        group.bench_with_input(
            BenchmarkId::new("BTreeMap", size),
            &operations,
            |b, operations| {
                b.iter_batched(
                    || map_with_capacity::<BTreeMap<_, _>>(&entries),
                    |map| black_box(scenario_mixed_usage(map, black_box(operations.as_slice()))),
                    BatchSize::SmallInput,
                );
            },
        );
    }

    group.finish();
}

fn bench_iter(c: &mut Criterion) {
    let mut group = c.benchmark_group("map/iter");

    for size in SIZES {
        let entries = entries(size);
        let alist = map_with_capacity::<AList<_, _>>(&entries);
        let hash_map = map_with_capacity::<HashMap<_, _>>(&entries);
        let btree_map = map_with_capacity::<BTreeMap<_, _>>(&entries);
        group.throughput(Throughput::Elements(size as u64));

        group.bench_function(BenchmarkId::new("AList", size), |b| {
            b.iter(|| black_box(scenario_iter(&alist)));
        });
        group.bench_function(BenchmarkId::new("HashMap", size), |b| {
            b.iter(|| black_box(scenario_iter(&hash_map)));
        });
        group.bench_function(BenchmarkId::new("BTreeMap", size), |b| {
            b.iter(|| black_box(scenario_iter(&btree_map)));
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_default,
    bench_with_capacity,
    bench_get_existing,
    bench_get_missing,
    bench_insert,
    bench_remove,
    bench_mixed_usage,
    bench_iter
);
criterion_main!(benches);

trait Map<K, V>: Default + Extend<(K, V)> {
    fn with_capacity(capacity: usize) -> Self;

    fn insert(&mut self, key: K, value: V) -> Option<V>;

    fn remove(&mut self, key: &K) -> Option<V>;

    fn get(&self, key: &K) -> Option<&V>;

    fn len(&self) -> usize;

    fn iter<'a>(&'a self) -> impl Iterator<Item = (&'a K, &'a V)> + 'a
    where
        K: 'a,
        V: 'a;
}

impl<K: FastEq, V> Map<K, V> for AList<K, V> {
    fn with_capacity(capacity: usize) -> Self {
        AList::with_capacity(capacity)
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        AList::insert(self, key, value)
    }

    fn remove(&mut self, key: &K) -> Option<V> {
        AList::remove(self, key)
    }

    fn get(&self, key: &K) -> Option<&V> {
        AList::get(self, key)
    }

    fn len(&self) -> usize {
        AList::len(self)
    }

    fn iter<'a>(&'a self) -> impl Iterator<Item = (&'a K, &'a V)> + 'a
    where
        K: 'a,
        V: 'a,
    {
        AList::iter(self)
    }
}

impl<K: Eq + Hash, V> Map<K, V> for HashMap<K, V> {
    fn with_capacity(capacity: usize) -> Self {
        HashMap::with_capacity(capacity)
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        HashMap::insert(self, key, value)
    }

    fn remove(&mut self, key: &K) -> Option<V> {
        HashMap::remove(self, key)
    }

    fn get(&self, key: &K) -> Option<&V> {
        HashMap::get(self, key)
    }

    fn len(&self) -> usize {
        HashMap::len(self)
    }

    fn iter<'a>(&'a self) -> impl Iterator<Item = (&'a K, &'a V)> + 'a
    where
        K: 'a,
        V: 'a,
    {
        HashMap::iter(self)
    }
}

impl<K: Ord, V> Map<K, V> for BTreeMap<K, V> {
    fn with_capacity(_: usize) -> Self {
        BTreeMap::new()
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        BTreeMap::insert(self, key, value)
    }

    fn remove(&mut self, key: &K) -> Option<V> {
        BTreeMap::remove(self, key)
    }

    fn get(&self, key: &K) -> Option<&V> {
        BTreeMap::get(self, key)
    }

    fn len(&self) -> usize {
        BTreeMap::len(self)
    }

    fn iter<'a>(&'a self) -> impl Iterator<Item = (&'a K, &'a V)> + 'a
    where
        K: 'a,
        V: 'a,
    {
        BTreeMap::iter(self)
    }
}
