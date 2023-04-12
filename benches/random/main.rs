use criterion::{
    black_box, criterion_group, criterion_main, measurement::Measurement, BatchSize,
    BenchmarkGroup, BenchmarkId, Criterion,
};
use rand::{
    distributions::{Bernoulli, Uniform},
    prelude::StdRng,
    Rng, SeedableRng,
};
use std::{collections::BTreeSet, time::Duration};

use veb_tree::{
    bitset::{ByteMapMarker, ByteSetMarker, VecDequeMarker},
    hash::HashMapMarker,
    tree::{Tree, TreeMarker},
    VebTree,
};
//VebTree
type U32Tree = Tree<
    u32,                                                                     // Key
    (),                                                                      // Value
    TreeMarker<ByteSetMarker, ByteMapMarker<VecDequeMarker, ByteSetMarker>>, // Summary
    // Children
    HashMapMarker<
        TreeMarker<ByteSetMarker, ByteMapMarker<VecDequeMarker, ByteSetMarker>>, // Child "tree"
    >,
>;

type U64Tree = Tree<
    u64,    //64
    &'static str,
    TreeMarker< //32
        TreeMarker< //16
            ByteSetMarker, ByteMapMarker<VecDequeMarker, ByteSetMarker>,
        >,
        HashMapMarker<//16 
            TreeMarker<ByteSetMarker, ByteMapMarker<VecDequeMarker, ByteSetMarker>>,
        >,
    >,
    HashMapMarker< // 32
        TreeMarker< // 16
            ByteSetMarker, ByteMapMarker<VecDequeMarker, ByteSetMarker>,
        >,
    >,
>;

trait VEBOperations {
    fn insert(&mut self, x: u32) -> bool;
    fn remove(&mut self, x: u32) -> bool;
    fn contains(&self, x: u32) -> bool;
    fn next(&self, x: u32) -> Option<u32>;
    fn prev(&self, x: u32) -> Option<u32>;
}

impl VEBOperations for Option<U32Tree> {
    fn insert(&mut self, x: u32) -> bool {
        let (v, r) = match self.take() {
            Some(mut v) => {
                let r = v.insert(x, ());
                (v, r.is_none())
            }
            None => (U32Tree::from_monad(x, ()), true),
        };
        *self = Some(v);
        r
    }

    fn remove(&mut self, x: u32) -> bool {
        let v = match self.take() {
            None => return false,
            Some(v) => v,
        };
        match v.remove(x) {
            Err(v) => {
                *self = Some(v);
                false
            }
            Ok((v, _)) => {
                *self = v;
                true
            }
        }
    }

    fn contains(&self, x: u32) -> bool {
        self.as_ref().and_then(|v| v.find(x)).is_some()
    }

    fn next(&self, x: u32) -> Option<u32> {
        self.as_ref()
            .and_then(|v| v.successor(x))
            .map(|v| v.0.into_or_clone())
    }

    fn prev(&self, x: u32) -> Option<u32> {
        self.as_ref()
            .and_then(|v| v.predecessor(x))
            .map(|v| v.0.into_or_clone())
    }
}
struct BTreeSetWrapper(BTreeSet<u32>);

impl VEBOperations for BTreeSetWrapper {
    fn insert(&mut self, x: u32) -> bool {
        self.0.insert(x)
    }

    fn remove(&mut self, x: u32) -> bool {
        self.0.remove(&x)
    }

    fn contains(&self, x: u32) -> bool {
        self.0.contains(&x)
    }

    fn next(&self, x: u32) -> Option<u32> {
        Some(*self.0.range(x..).next()?)
    }

    fn prev(&self, x: u32) -> Option<u32> {
        Some(*self.0.range(..=x).next_back()? as u32)
    }
}

fn for_all_widths<'a, M: Measurement, Tree, Ret>(
    mut group: BenchmarkGroup<'a, M>,
    mut maker: impl FnMut(&mut StdRng, usize) -> Tree,
    mut test: impl FnMut(&mut Tree, u32) -> Ret,
) {
    group.warm_up_time(Duration::from_millis(1000));
    group.measurement_time(Duration::from_millis(2000));

    for bits in 27..=30 {
        let capacity = 1 << bits;
        let distr = Uniform::from(0..capacity);

        let mut rng = StdRng::seed_from_u64(0);

        let mut s = maker(&mut rng, bits);
        group.bench_function(BenchmarkId::from_parameter(bits), |b| {
            b.iter_batched(
                || rng.sample(distr),
                |x| test(&mut s, x),
                BatchSize::SmallInput,
            );
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
        let mut s = BTreeSetWrapper(BTreeSet::new());
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
    // for_all_widths(
    //     c.benchmark_group(format!("remove-veb")),
    //     veb_maker,
    //     |s, x| VEBOperations::remove(black_box(s), x),
    // );
    // for_all_widths(
    //     c.benchmark_group(format!("contains-veb")),
    //     veb_maker,
    //     |s, x| VEBOperations::contains(black_box(s), x),
    // );
    // for_all_widths(c.benchmark_group(format!("next-veb")), veb_maker, |s, x| {
    //     VEBOperations::next(black_box(s), x)
    // });
    // for_all_widths(c.benchmark_group(format!("prev-veb")), veb_maker, |s, x| {
    //     VEBOperations::prev(black_box(s), x)
    // });

    for_all_widths(
        c.benchmark_group(format!("insert-btree")),
        btree_maker,
        |s, x| black_box(s).insert(x),
    );
    // for_all_widths(
    //     c.benchmark_group(format!("remove-btree")),
    //     btree_maker,
    //     |s, x| black_box(s).remove(x),
    // );
    // for_all_widths(
    //     c.benchmark_group(format!("contains-btree")),
    //     btree_maker,
    //     |s, x| black_box(s).contains(x),
    // );
    // for_all_widths(
    //     c.benchmark_group(format!("next-btree")),
    //     btree_maker,
    //     |s, x| black_box(s).next(x),
    // );
    // for_all_widths(
    //     c.benchmark_group(format!("prev-btree")),
    //     btree_maker,
    //     |s, x| black_box(s).prev(x),
    //);
}

mod perf;

criterion_group! {
    name = benches;
    // This can be any expression that returns a `Criterion` object.
    config = Criterion::default().with_profiler(perf::FlamegraphProfiler::new(100));
    targets = criterion_benchmark
}
criterion_main!(benches);
