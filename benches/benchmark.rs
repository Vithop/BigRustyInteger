use criterion::*;
use std::u64;
use std::iter;

use big_rusty_integer::{BigInt};


pub fn generate_list_of_big_rusty_int(size: usize) -> Vec<BigInt> {
    let mut digits: Vec<u64> = Vec::with_capacity(size);
    let mut list_of_big_ints = Vec::<BigInt>::with_capacity(size);
    for i in 1..=size {
        digits.push(i as u64);
        list_of_big_ints.push(BigInt::new(digits.clone()));
    }
    return list_of_big_ints;
}

pub fn generate_list_of_big_rusty_int_from_list_of_sizes(size_list: Vec<u64>) -> Vec<BigInt> {
    let mut list_of_big_ints = Vec::<BigInt>::with_capacity(size_list.len());
    for i in size_list {
        list_of_big_ints.push(BigInt::new((1..=i).collect()));
    }
    return list_of_big_ints;
}

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("BigInt 2 ", |b| b.iter(|| BigInt::new(black_box(vec![2]))));
}


fn add_bench(c: &mut Criterion) {
    let plot_config = PlotConfiguration::default()
        .summary_scale(AxisScale::Linear);

    let mut group = c.benchmark_group("big_rusty_int_add");
    group.plot_config(plot_config);
    
    let big_rusty_int_list = generate_list_of_big_rusty_int_from_list_of_sizes(vec![1,10,20,40,100,160,320,640,1280]);
    let mut a = BigInt::new(vec![1]);
    for i in big_rusty_int_list {
        // i.print_digits();
        group.bench_function(BenchmarkId::from_parameter(i.most_sig_digit()), |b| b.iter(||a += black_box(&i) ));
    }
    group.finish();
}

criterion_group!(benches, add_bench);
criterion_main!(benches);