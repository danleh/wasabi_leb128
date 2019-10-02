#![feature(test)]

extern crate test;

use leb128::{read, write};
use leb128_daniel::{ReadLeb128, WriteLeb128};
use test::Bencher;

#[test]
fn test_equal() {
    for i in 0..1000000u64 {
        let mut vec1 = Vec::new();
        let mut vec2 = Vec::new();
        vec1.write_leb128(i).unwrap();
        write::unsigned(&mut vec2, i).unwrap();
        assert_eq!(&vec1, &vec2);
    }
}

//#[bench]
//fn unsigned_daniel(bencher: &mut Bencher) {
//    bencher.iter(|| {
//        for i in 0..1000000u64 {
//            let mut vec = Vec::new();
//            vec.write_leb128(i).unwrap();
//            let _o: u64 = (&mut &vec[..]).read_leb128().unwrap();
//        }
//    })
//}
//
//#[bench]
//fn unsigned_crates_io(bencher: &mut Bencher) {
//    bencher.iter(|| {
//        for i in 0..1000000u64 {
//            let mut vec = Vec::new();
//            write::unsigned(&mut vec, i).unwrap();
//            let _o: u64 = read::unsigned(&mut &vec[..]).unwrap();
//        }
//    })
//}

use std::i16;

#[bench]
fn signed_daniel(bencher: &mut Bencher) {
    bencher.iter(|| {
        for i in -100000..=100000 {
            let mut vec = Vec::new();
            vec.write_leb128(i).unwrap();
            let o = leb128_daniel::us(&mut &vec[..]);
//            let o: i16 = (&mut &vec[..]).read_leb128().unwrap();
//            let o: i16 = (&mut &vec![0x80u8, 0x80, 0x01][..]).read_leb128().unwrap();
//            test::black_box(vec);
            test::black_box(o);
        }
    })
}

#[bench]
fn signed_crates_io(bencher: &mut Bencher) {
    bencher.iter(|| {
        for i in -100000..=100000 {
            let mut vec = Vec::new();
            write::signed(&mut vec, i as i64).unwrap();
            let o = leb128_daniel::them(&mut &vec[..]);
//            let o: i16 = read::signed(&mut &vec[..]).unwrap() as i16;
//            let o: i16 = read::signed(&mut &vec![0x80u8, 0x80, 0x01][..]).unwrap() as i16;
//            test::black_box(vec);
            test::black_box(o);
        }
    })
}

use std::{i128, i64};

/// Utility macro to check for overflow errors when converting from a wider to a narrow type.
macro_rules! detect_overflow {
    ($original_value: expr, $T: ty, $U: ty) => ({
        // Encode as the wider type.
        let original_value: $T = $original_value;
        let mut buf = Vec::new();
        buf.write_leb128(original_value);

        // Decode as the narrower type.
        let decoded_value: Result<$U, _> = read::signed(&mut &buf[..]);

        // If the input value cannot be represented without loss in the target type,
        // read_leb128() should have Err()'d.
        use std::convert::TryFrom;
        let expect_overflow = <$U>::try_from(original_value).is_err();
        if expect_overflow {
            assert!(
                decoded_value.is_err(),
                "expected overflow error when decoding {} {:?} ({:?} in LEB128) as {}, but got {:?}",
                stringify!($T),
                original_value,
                buf,
                stringify!($U),
                decoded_value
            );
        } else {
            assert_eq!(original_value, decoded_value.unwrap() as $T);
        }
    })
}

#[test]
fn test_detect_overflow() {
    let values = [
        // Those two overflow because they use more bytes than possible for an i16 (5 instead of max 3).
        i128::MIN,
        i128::MIN + 1,
        // Should overflow because even though it encodes to 3 bytes only, the high bits of the
        // last byte are too large to be representable in an i16.
        i64::MIN as i128 - 1,
        // Next seven should NOT overflow, they are valid i16s as well.
        i64::MIN as i128,
        i64::MIN as i128 + 1,
        -1,
        0,
        1,
        i64::MAX as i128 - 1,
        i64::MAX as i128,
        // Overflow because of high bits in last byte.
        i64::MAX as i128 + 1,
        // Overflow because too many bytes for i16 LEB128 (5 instead of 3).
        i128::MAX - 1,
        i128::MAX,
    ];

    for &i in &values {
        detect_overflow!(i, i128, i64)
    }
}

pub fn theirs(i: i64, vec: &mut Vec<u8>) -> i64 {
    vec.write_leb128(i).unwrap();
    (&mut &vec[..]).read_leb128().unwrap()
//
//    let mut vec = Vec::new();
//    write::signed(&mut vec, i).unwrap();
//    let _o = read::signed(&mut &vec[..]).unwrap();
}

fn main() {
    theirs(std::env::args().len() as i64, &mut vec![]);
}