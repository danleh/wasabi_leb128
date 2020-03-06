#![feature(test)]

extern crate test;

use std::hint::black_box;
use test::Bencher;

use wasabi_leb128::{ReadLeb128, WriteLeb128};

const VALUES: [i64; 13] = [
    -100000, -10000, -1000, -100, -10, -1, 0, 1, 10, 100, 1000, 10000, 100000,
];
const ITERATIONS: usize = 10_000;

// Use the gimli.rs leb128 crate as a baseline, since it has already been optimized a bit, it seems.

#[bench]
fn bench_read_gimli(bencher: &mut Bencher) {
    for &i in &VALUES {
        let mut vec = Vec::new();
        gimli_leb128::write::signed(&mut vec, i).unwrap();
        bencher.iter(|| {
            for _ in 0..ITERATIONS {
                let result: i64 = gimli_leb128::read::signed(&mut vec.as_slice()).unwrap();
                black_box(result);
            }
        })
    }
}

#[bench]
fn bench_read_ours(bencher: &mut Bencher) {
    for &i in &VALUES {
        let mut vec = Vec::new();
        vec.write_leb128(i).unwrap();
        bencher.iter(|| {
            for _ in 0..ITERATIONS {
                let result: i64 = vec.as_slice().read_leb128().unwrap().0;
                black_box(result);
            }
        })
    }
}

#[bench]
fn bench_write_gimli(bencher: &mut Bencher) {
    for &i in &VALUES {
        let mut vec = Vec::new();
        bencher.iter(|| {
            for _ in 0..ITERATIONS {
                black_box(gimli_leb128::write::signed(&mut vec, i).unwrap());
            }
        })
    }
}

#[bench]
fn bench_write_ours(bencher: &mut Bencher) {
    for &i in &VALUES {
        let mut vec = Vec::new();
        bencher.iter(|| {
            for _ in 0..ITERATIONS {
                black_box(vec.write_leb128(i).unwrap());
            }
        })
    }
}
