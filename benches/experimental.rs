use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput};
use gen_value::{GenVec, Incrementable};
use rand::prelude::*;
use std::{
    collections::{BTreeMap, HashMap},
    ops::AddAssign,
};

#[derive(Clone, Copy, Debug)]
struct Value<const N: usize>([u8; N]);

impl<const N: usize> Default for Value<N> {
    fn default() -> Self {
        Self([0; N])
    }
}

fn create_vec_and_indexes<T: Default>(len: usize) -> (Vec<T>, Vec<usize>) {
    let mut v: Vec<T> = Vec::default();
    (0..len).for_each(|_| v.push(T::default()));
    let indexes = (0..len).collect::<Vec<_>>();
    (v, indexes)
}

fn create_genvec_and_indexes<
    T: Default,
    G: Clone + Default + PartialOrd + Incrementable,
    I: Clone + Default + Into<usize> + Incrementable,
>(
    len: usize,
) -> (GenVec<T, G, I>, Vec<(I, G)>) {
    let mut gen_vec: GenVec<T, G, I> = GenVec::default();
    let indexes = (0..len)
        .map(|_| gen_vec.insert(T::default()).unwrap())
        .collect::<Vec<_>>();
    (gen_vec, indexes)
}

fn create_map_and_indexes<T: Default, C: FromIterator<(usize, T)>>(len: usize) -> (C, Vec<usize>) {
    let v = (0..len).map(|k| (k, T::default())).collect::<C>();
    let indexes = (0..len).collect::<Vec<_>>();
    (v, indexes)
}

// Set an element

#[allow(clippy::too_many_lines)]
fn iter_sequentially<T: Copy + Default + AddAssign>(c: &mut Criterion) {
    let mut group = c.benchmark_group("iter_sequentially");
    for n in [32, 64, 256, 1024] {
        group.throughput(Throughput::Elements(u64::try_from(n).unwrap()));
        macro_rules! bench_it {
            ($title:expr, $i:expr) => {
                group.bench_with_input(BenchmarkId::new(format!("{}", $title), n), &n, $i);
            };
        }

        bench_it!("GenVec::get", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (data, indexes) = create_genvec_and_indexes::<T, usize, usize>(n);
                    (data, indexes)
                },
                |(data, indexes)| {
                    let mut total = T::default();
                    for idx in indexes.iter() {
                        let value = data.get(*idx).unwrap();
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("GenVec::get_unchecked", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (data, indexes) = create_genvec_and_indexes::<T, usize, usize>(n);
                    (data, indexes)
                },
                |(data, indexes)| {
                    let mut total = T::default();
                    for idx in indexes.iter() {
                        let value = unsafe { data.get_unchecked(idx.0) };
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("Vec::iter", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (data, _) = create_vec_and_indexes::<T>(n);
                    data
                },
                move |data| {
                    let mut total = T::default();
                    for value in data.iter() {
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("HashMap::iter", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (data, _) = create_map_and_indexes::<T, HashMap<usize, T>>(n);
                    data
                },
                move |data| {
                    let mut total = T::default();
                    for (_, value) in data.iter() {
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("HashMap::values", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (data, _) = create_map_and_indexes::<T, HashMap<usize, T>>(n);
                    data
                },
                move |data| {
                    let mut total = T::default();
                    for value in data.values() {
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("BTreeMap::iter", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (data, _) = create_map_and_indexes::<T, BTreeMap<usize, T>>(n);
                    data
                },
                move |data| {
                    let mut total = T::default();
                    for (_, value) in data.iter() {
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("BTreeMap::values", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (data, _) = create_map_and_indexes::<T, BTreeMap<usize, T>>(n);
                    data
                },
                move |data| {
                    let mut total = T::default();
                    for value in data.values() {
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });
    }
    group.finish();
}

#[allow(clippy::too_many_lines)]
fn iter_sequentially_half_elements_removed<T: Copy + Default + AddAssign>(c: &mut Criterion) {
    let mut group = c.benchmark_group("iter_sequentially_half_elements_removed");
    let mut rng = thread_rng();
    for n in [32, 64, 256, 1024] {
        group.throughput(Throughput::Elements(u64::try_from(n).unwrap()));
        macro_rules! bench_it {
            ($title:expr, $i:expr) => {
                group.bench_with_input(BenchmarkId::new(format!("{}", $title), n), &n, $i);
            };
        }

        bench_it!("GenVec::get", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (mut data, mut indexes) = create_genvec_and_indexes::<T, usize, usize>(n);
                    indexes.shuffle(&mut rng);
                    (0..(n / 2)).for_each(|_| {
                        data.remove(indexes.pop().unwrap()).unwrap();
                    });
                    (data, indexes)
                },
                |(data, indexes)| {
                    let mut total = T::default();
                    for idx in indexes.iter() {
                        let value = data.get(*idx).unwrap();
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("GenVec::get (sorted indexes)", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (mut data, mut indexes) = create_genvec_and_indexes::<T, usize, usize>(n);
                    indexes.shuffle(&mut rng);
                    (0..(n / 2)).for_each(|_| {
                        data.remove(indexes.pop().unwrap()).unwrap();
                    });
                    indexes.sort_unstable();
                    (data, indexes)
                },
                |(data, indexes)| {
                    let mut total = T::default();
                    for idx in indexes.iter() {
                        let value = data.get(*idx).unwrap();
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("GenVec::get_unchecked", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (mut data, mut indexes) = create_genvec_and_indexes::<T, usize, usize>(n);
                    indexes.shuffle(&mut rng);
                    (0..(n / 2)).for_each(|_| {
                        data.remove(indexes.pop().unwrap()).unwrap();
                    });
                    (data, indexes)
                },
                |(data, indexes)| {
                    let mut total = T::default();
                    for idx in indexes.iter() {
                        let value = unsafe { data.get_unchecked(idx.0) };
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("GenVec::get_unchecked (sorted)", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (mut data, mut indexes) = create_genvec_and_indexes::<T, usize, usize>(n);
                    indexes.shuffle(&mut rng);
                    (0..(n / 2)).for_each(|_| {
                        data.remove(indexes.pop().unwrap()).unwrap();
                    });
                    indexes.sort_unstable();
                    (data, indexes)
                },
                |(data, indexes)| {
                    let mut total = T::default();
                    for idx in indexes.iter() {
                        let value = unsafe { data.get_unchecked(idx.0) };
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("Vec::iter", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (mut data, _) = create_vec_and_indexes::<T>(n);
                    data.resize(n / 2, T::default());
                    data
                },
                move |data| {
                    let mut total = T::default();
                    for value in data.iter() {
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("HashMap::iter", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (mut data, mut indexes) = create_map_and_indexes::<T, HashMap<usize, T>>(n);
                    indexes.shuffle(&mut rng);
                    (0..(n / 2)).for_each(|_| {
                        data.remove(&indexes.pop().unwrap()).unwrap();
                    });
                    data
                },
                move |data| {
                    let mut total = T::default();
                    for (_, value) in data.iter() {
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("HashMap::values", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (mut data, mut indexes) = create_map_and_indexes::<T, HashMap<usize, T>>(n);
                    indexes.shuffle(&mut rng);
                    (0..(n / 2)).for_each(|_| {
                        data.remove(&indexes.pop().unwrap()).unwrap();
                    });
                    data
                },
                move |data| {
                    let mut total = T::default();
                    for value in data.values() {
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("BTreeMap::iter", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (mut data, mut indexes) =
                        create_map_and_indexes::<T, BTreeMap<usize, T>>(n);
                    indexes.shuffle(&mut rng);
                    (0..(n / 2)).for_each(|_| {
                        data.remove(&indexes.pop().unwrap()).unwrap();
                    });
                    data
                },
                move |data| {
                    let mut total = T::default();
                    for (_, value) in data.iter() {
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("BTreeMap::values", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (mut data, mut indexes) =
                        create_map_and_indexes::<T, BTreeMap<usize, T>>(n);
                    indexes.shuffle(&mut rng);
                    (0..(n / 2)).for_each(|_| {
                        data.remove(&indexes.pop().unwrap()).unwrap();
                    });
                    data
                },
                move |data| {
                    let mut total = T::default();
                    for value in data.values() {
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });
    }
    group.finish();
}

#[allow(clippy::too_many_lines)]
fn random_get_all<T: Copy + Default + AddAssign>(c: &mut Criterion) {
    let mut group = c.benchmark_group("random_get_all");
    let mut rng = thread_rng();
    // let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    // group.plot_config(plot_config);
    // for n in [8, 16, 32, 64, 128, 256, 512, 1024] {
    for n in [32, 64, 256, 1024] {
        group.throughput(Throughput::Elements(u64::try_from(n).unwrap()));
        macro_rules! bench_it {
            ($title:expr, $i:expr) => {
                group.bench_with_input(BenchmarkId::new(format!("{}", $title), n), &n, $i);
            };
        }

        bench_it!("GenVec::get", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (data, mut indexes) = create_genvec_and_indexes::<T, usize, usize>(n);
                    indexes.shuffle(&mut rng);
                    (data, indexes)
                },
                |(data, indexes)| {
                    let mut total = T::default();
                    for idx in indexes.iter() {
                        let value = data.get(*idx).unwrap();
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("GenVec::get_unchecked", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (data, mut indexes) = create_genvec_and_indexes::<T, usize, usize>(n);
                    indexes.shuffle(&mut rng);
                    (data, indexes)
                },
                |(data, indexes)| {
                    let mut total = T::default();
                    for idx in indexes.iter() {
                        let value = unsafe { data.get_unchecked(idx.0) };
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("Vec::get", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (data, mut indexes) = create_vec_and_indexes::<T>(n);
                    indexes.shuffle(&mut rng);
                    (data, indexes)
                },
                move |(data, indexes)| {
                    let mut total = T::default();
                    for idx in indexes.iter() {
                        let value = data.get(*idx).unwrap();
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("Vec::get_unchecked", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (data, mut indexes) = create_vec_and_indexes::<T>(n);
                    indexes.shuffle(&mut rng);
                    (data, indexes)
                },
                move |(data, indexes)| {
                    let mut total = T::default();
                    for idx in indexes.iter() {
                        let value = unsafe { data.get_unchecked(*idx) };
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("HashMap::get", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (data, mut indexes) = create_map_and_indexes::<T, HashMap<usize, T>>(n);
                    indexes.shuffle(&mut rng);
                    (data, indexes)
                },
                move |(data, indexes)| {
                    let mut total = T::default();
                    for idx in indexes.iter() {
                        let value = data.get(idx).unwrap();
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });

        bench_it!("BTreeMap::get", |b, &n| {
            b.iter_batched_ref(
                || {
                    let (data, mut indexes) = create_map_and_indexes::<T, BTreeMap<usize, T>>(n);
                    indexes.shuffle(&mut rng);
                    (data, indexes)
                },
                move |(data, indexes)| {
                    let mut total = T::default();
                    for idx in indexes.iter() {
                        let value = data.get(idx).unwrap();
                        total += *value;
                    }
                    total
                },
                BatchSize::LargeInput,
            );
        });
    }
    group.finish();
}

macro_rules! ty_str {
    ($type:ty) => {
        std::any::type_name::<$type>()
    };
}

fn random_get_one_type<T: Copy + Default>(c: &mut Criterion) {
    let mut group = c.benchmark_group("random_get_one");
    let mut rng = thread_rng();

    // let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    // group.plot_config(plot_config);
    group.throughput(Throughput::Elements(u64::try_from(1).unwrap()));
    for n in [32, 64, 256, 1024] {
        // for n in [8, 16, 32, 64, 128, 256, 512, 1024] {
        macro_rules! bench_it {
            ($title:expr, $i:expr) => {
                group.bench_with_input(BenchmarkId::new(format!("{}", $title), n), &n, $i);
            };
        }

        macro_rules! bench_gen_vec {
            ($gen_ty:ty) => {
                bench_it!(
                    format!(
                        "GenVec::get::({}, {}, usize)",
                        ty_str!(T),
                        stringify!($gen_ty)
                    ),
                    |b, &i| {
                        b.iter_batched_ref(
                            || {
                                let (data, mut indexes) =
                                    create_genvec_and_indexes::<T, $gen_ty, usize>(i);
                                indexes.shuffle(&mut rng);
                                (data, indexes.into_iter().cycle())
                            },
                            |(data, index)| *data.get(index.next().unwrap()).unwrap(),
                            BatchSize::SmallInput,
                        );
                    }
                );

                bench_it!(
                    format!(
                        "GenVec::get_unchecked::({}, {}, usize)",
                        ty_str!(T),
                        stringify!($gen_ty)
                    ),
                    |b, &i| {
                        b.iter_batched_ref(
                            || {
                                let (data, mut indexes) =
                                    create_genvec_and_indexes::<T, $gen_ty, usize>(i);
                                indexes.shuffle(&mut rng);
                                (data, indexes.into_iter().cycle())
                            },
                            |(data, index)| unsafe { *data.get_unchecked(index.next().unwrap().0) },
                            BatchSize::SmallInput,
                        );
                    }
                );
            };
        }

        bench_gen_vec!(usize);

        bench_it!(format!("Vec::get::({})", ty_str!(T)), |b, &i| {
            b.iter_batched_ref(
                || {
                    let (data, mut indexes) = create_vec_and_indexes::<T>(i);
                    indexes.shuffle(&mut rng);
                    (data, indexes.into_iter().cycle())
                },
                |(data, index)| *data.get(index.next().unwrap()).unwrap(),
                BatchSize::SmallInput,
            );
        });

        bench_it!(format!("Vec::get_unchecked::({})", ty_str!(T)), |b, &i| {
            b.iter_batched_ref(
                || {
                    let (data, mut indexes) = create_vec_and_indexes::<T>(i);
                    indexes.shuffle(&mut rng);
                    (data, indexes.into_iter().cycle())
                },
                |(data, index)| unsafe { *data.get_unchecked(index.next().unwrap()) },
                BatchSize::SmallInput,
            );
        });

        bench_it!(format!("HashMap::get::({})", ty_str!(T)), |b, &i| {
            b.iter_batched_ref(
                || {
                    let (data, mut indexes) = create_map_and_indexes::<T, HashMap<usize, T>>(i);
                    indexes.shuffle(&mut rng);
                    (data, indexes.into_iter().cycle())
                },
                |(data, index)| *data.get(&index.next().unwrap()).unwrap(),
                BatchSize::SmallInput,
            );
        });

        bench_it!(format!("BTreeMap::get::({})", ty_str!(T)), |b, &i| {
            b.iter_batched_ref(
                || {
                    let (data, mut indexes) = create_map_and_indexes::<T, BTreeMap<usize, T>>(i);
                    indexes.shuffle(&mut rng);
                    (data, indexes.into_iter().cycle())
                },
                |(data, index)| *data.get(&index.next().unwrap()).unwrap(),
                BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    iter_sequentially::<usize>,
    iter_sequentially_half_elements_removed::<usize>,
    random_get_all::<usize>,
    random_get_one_type::<usize>,
);
criterion_main!(benches);
