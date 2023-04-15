use criterion::{
    black_box, criterion_group, criterion_main, measurement::Measurement, BatchSize,
    BenchmarkGroup, BenchmarkId, Criterion,
};
use rand::{
    distributions::{Bernoulli, Uniform},
    prelude::StdRng,
    Rng, SeedableRng,
};
use std::{collections::BTreeMap, time::Duration};

use veb_tree::{
    markers::{Marker32, VebTreeType},
    SizedVebTree, VebTree,
};

// type Data = f32;
// const DATA: Data = 5.4;

type Data = ();
const DATA: Data = ();

type U32Tree = SizedVebTree<VebTreeType<u32, Data, Marker32>>;

trait VEBOperations {
    fn len(&self) -> usize;
    fn insert(&mut self, x: u32) -> Option<Data>;
    fn remove(&mut self, x: u32) -> Option<Data>;
    fn find(&self, x: u32) -> Option<&Data>;
    fn next(&self, x: u32) -> Option<(u32, &Data)>;
    fn prev(&self, x: u32) -> Option<(u32, &Data)>;
    fn find_mut(&mut self, x: u32) -> Option<&mut Data>;
    fn next_mut(&mut self, x: u32) -> Option<(u32, &mut Data)>;
    fn prev_mut(&mut self, x: u32) -> Option<(u32, &mut Data)>;
}

impl VEBOperations for Option<U32Tree> {
    fn len(&self) -> usize {
        self.as_ref().map_or(0, U32Tree::len)
    }
    fn insert(&mut self, x: u32) -> Option<Data> {
        let (v, r) = match self.take() {
            Some(mut v) => {
                let r = v.insert(x, DATA);
                (v, r)
            }
            None => (U32Tree::from_monad(x, DATA), None),
        };
        *self = Some(v);
        r.map(|(_k, v)| v)
    }

    fn remove(&mut self, x: u32) -> Option<Data> {
        let t = match self.take() {
            None => return None,
            Some(v) => v,
        };
        match t.remove(x) {
            Err(t) => {
                *self = Some(t);
                None
            }
            Ok((t, (_k, v))) => {
                *self = t;
                Some(v)
            }
        }
    }

    fn find(&self, x: u32) -> Option<&Data> {
        self.as_ref().and_then(|v| v.find(x)).map(|(_k, v)| v)
    }

    fn next(&self, x: u32) -> Option<(u32, &Data)> {
        self.as_ref()
            .and_then(|v| v.successor(x))
            .map(|(k, v)| (k.into_or_clone(), v))
    }

    fn prev(&self, x: u32) -> Option<(u32, &Data)> {
        self.as_ref()
            .and_then(|v| v.predecessor(x))
            .map(|(k, v)| (k.into_or_clone(), v))
    }

    fn find_mut(&mut self, x: u32) -> Option<&mut Data> {
        self.as_mut().and_then(|v| v.find_mut(x)).map(|(_k, v)| v)
    }

    fn next_mut(&mut self, x: u32) -> Option<(u32, &mut Data)> {
        self.as_mut()
            .and_then(|v| v.successor_mut(x))
            .map(|(k, v)| (k.into_or_clone(), v))
    }

    fn prev_mut(&mut self, x: u32) -> Option<(u32, &mut Data)> {
        self.as_mut()
            .and_then(|v| v.predecessor_mut(x))
            .map(|(k, v)| (k.into_or_clone(), v))
    }
}
struct BTreeSetWrapper(BTreeMap<u32, Data>);

impl VEBOperations for BTreeSetWrapper {
    fn len(&self) -> usize {
        self.0.len()
    }
    fn insert(&mut self, x: u32) -> Option<Data> {
        self.0.insert(x, DATA)
    }

    fn remove(&mut self, x: u32) -> Option<Data> {
        self.0.remove(&x)
    }

    fn find(&self, x: u32) -> Option<&Data> {
        self.0.get(&x)
    }

    fn next(&self, x: u32) -> Option<(u32, &Data)> {
        self.0.range(x..).next().map(|(k, v)| (k.clone(), v))
    }

    fn prev(&self, x: u32) -> Option<(u32, &Data)> {
        self.0.range(..=x).next_back().map(|(k, v)| (k.clone(), v))
    }

    fn find_mut(&mut self, x: u32) -> Option<&mut Data> {
        self.0.get_mut(&x)
    }

    fn next_mut(&mut self, x: u32) -> Option<(u32, &mut Data)> {
        self.0.range_mut(x..).next().map(|(k, v)| (k.clone(), v))
    }

    fn prev_mut(&mut self, x: u32) -> Option<(u32, &mut Data)> {
        self.0
            .range_mut(..=x)
            .next_back()
            .map(|(k, v)| (k.clone(), v))
    }
}

fn for_all_widths<'a, M: Measurement, Tree, Ret>(
    mut group: BenchmarkGroup<'a, M>,
    mut maker: impl FnMut(&mut StdRng, usize) -> Tree,
    mut test: impl FnMut(&mut Tree, u32) -> Ret,
) {
    group.warm_up_time(Duration::from_millis(1000));
    group.measurement_time(Duration::from_millis(2000));

    for bits in 4..=30 {
        let capacity = 1 << bits;
        let distr = Uniform::from(0..capacity);
        let mut rng = StdRng::seed_from_u64(0);
        let mut s = None;
        group.bench_function(BenchmarkId::from_parameter(bits), |b| {
            let s = s.get_or_insert_with(|| maker(&mut rng, bits));
            b.iter_batched(|| rng.sample(distr), |x| test(s, x), BatchSize::SmallInput);
        });
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    let distr = Bernoulli::from_ratio(1, 2).unwrap();

    let veb_maker = |rng: &mut StdRng, bits| {
        let mut s = None;
        for x in 0..(1u32 << bits) {
            if rng.sample(&distr) {
                VEBOperations::insert(&mut s, x);
            }
        }
        s
    };

    let btree_maker = |rng: &mut StdRng, bits: usize| {
        let mut s = BTreeSetWrapper(BTreeMap::new());
        for x in 0..(1 << bits) {
            if rng.sample(&distr) {
                VEBOperations::insert(&mut s, x);
            }
        }
        s
    };

    for_all_widths(
        c.benchmark_group(format!("insert-veb")),
        veb_maker,
        |s, x| VEBOperations::insert(black_box(s), x),
    );
    for_all_widths(
        c.benchmark_group(format!("remove-veb")),
        veb_maker,
        |s, x| VEBOperations::remove(black_box(s), x),
    );
    for_all_widths(c.benchmark_group(format!("find-veb")), veb_maker, |s, x| {
        VEBOperations::find(black_box(s), x).is_some()
    });
    for_all_widths(c.benchmark_group(format!("next-veb")), veb_maker, |s, x| {
        VEBOperations::next(black_box(s), x).is_some()
    });
    for_all_widths(c.benchmark_group(format!("prev-veb")), veb_maker, |s, x| {
        VEBOperations::prev(black_box(s), x).is_some()
    });
    for_all_widths(
        c.benchmark_group(format!("find-mut-veb")),
        veb_maker,
        |s, x| VEBOperations::find_mut(black_box(s), x).is_some(),
    );
    for_all_widths(
        c.benchmark_group(format!("next-mut-veb")),
        veb_maker,
        |s, x| VEBOperations::next_mut(black_box(s), x).is_some(),
    );
    for_all_widths(
        c.benchmark_group(format!("prev-mut-veb")),
        veb_maker,
        |s, x| VEBOperations::prev_mut(black_box(s), x).is_some(),
    );

    for_all_widths(
        c.benchmark_group(format!("insert-btree")),
        btree_maker,
        |s, x| black_box(s).insert(x),
    );
    for_all_widths(
        c.benchmark_group(format!("remove-btree")),
        btree_maker,
        |s, x| black_box(s).remove(x),
    );
    for_all_widths(
        c.benchmark_group(format!("find-btree")),
        btree_maker,
        |s, x| black_box(s).find(x).is_some(),
    );
    for_all_widths(
        c.benchmark_group(format!("next-btree")),
        btree_maker,
        |s, x| black_box(s).next(x).is_some(),
    );
    for_all_widths(
        c.benchmark_group(format!("prev-btree")),
        btree_maker,
        |s, x| black_box(s).prev(x).is_some(),
    );
    for_all_widths(
        c.benchmark_group(format!("find-mut-btree")),
        btree_maker,
        |s, x| black_box(s).find_mut(x).is_some(),
    );
    for_all_widths(
        c.benchmark_group(format!("next-mut-btree")),
        btree_maker,
        |s, x| black_box(s).next_mut(x).is_some(),
    );
    for_all_widths(
        c.benchmark_group(format!("prev-mut-btree")),
        btree_maker,
        |s, x| black_box(s).prev_mut(x).is_some(),
    );
}

mod perf;

criterion_group! {
    name = benches;
    // This can be any expression that returns a `Criterion` object.
    config = Criterion::default().with_profiler(perf::FlamegraphProfiler::new(100));
    targets = criterion_benchmark
}
criterion_main!(benches);
