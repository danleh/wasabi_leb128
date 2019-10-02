#![feature(test)]

extern crate test;

use test::Bencher;
use std::hint::black_box;

const VALUES: [i64; 13] = [-100000, -10000, -1000, -100, -10, -1, 0, 1, 10, 100, 1000, 10000, 100000];
const ITERATIONS: usize = 10_000;

#[bench]
fn bench_write_gimli(bencher: &mut Bencher) {
    let mut vec = Vec::new();
    for &i in &VALUES {
        bencher.iter(|| {
            for _ in 0..ITERATIONS {
                black_box(gimli_leb128::write::signed(&mut vec, i).unwrap());
            }
        })
    }
}

#[bench]
fn bench_write_ours(bencher: &mut Bencher) {
    let mut vec = Vec::new();
    for &i in &VALUES {
        bencher.iter(|| {
            for _ in 0..ITERATIONS {
                use leb128::WriteLeb128;
                black_box(vec.write_leb128(i).unwrap());
            }
        })
    }
}

// TODO read benchmarks
