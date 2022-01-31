use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::u64;
use big_rusty_integer::BigInt;

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("BigInt 2 ", |b| b.iter(|| BigInt::new(vec![2])));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);