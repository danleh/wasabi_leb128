use crate::{ReadLeb128, WriteLeb128};

use std::{i16, i32, u16, u32};

/// Utility function that gives back a vector of bytes with the LEB128 representation of x.
fn write_leb128<T>(x: T) -> Vec<u8>
where
    Vec<u8>: WriteLeb128<T>,
{
    let mut buf = Vec::new();
    buf.write_leb128(x).expect("writing to a vector should never fail, since all input values of an integer type T can be represented in LEB128");
    buf
}

// Test some manually selected values encode to the right LEB128 bytes.

#[test]
fn known_encodings_are_correct_unsigned() {
    assert_eq!(write_leb128(0_u32), [0x00]);
    assert_eq!(write_leb128(1_u32), [0x01]);
    assert_eq!(write_leb128(127_u32), [0x7f]);
    assert_eq!(write_leb128(128_u32), [0x80, 0x01]);
    assert_eq!(write_leb128(16256_u32), [0x80, 0x7f]);
}

#[test]
fn known_encodings_are_correct_signed() {
    assert_eq!(write_leb128(0_i32), [0x00]);
    assert_eq!(write_leb128(1_i32), [0x01]);
    assert_eq!(write_leb128(-1_i32), [0x7f]);
    assert_eq!(write_leb128(127_i32), [0xff, 0x00]);
    assert_eq!(write_leb128(-127_i32), [0x81, 0x7f]);
    assert_eq!(write_leb128(128_i32), [0x80, 0x01]);
    assert_eq!(write_leb128(-128_i32), [0x80, 0x7f]);
}

// Exhaustively test that decode(encode(value)) == value for u16 and i16.

#[test]
fn roundtrips_u16() {
    for u in u16::MIN..=u16::MAX {
        let buf = write_leb128(u);
        let (u_decode, _): (u16, _) = buf
            .as_slice()
            .read_leb128()
            .expect("valid u16 should be possible to decode");
        assert_eq!(u, u_decode, "\nLEB128 bytes: {:?}", buf);
    }
}

#[test]
fn roundtrips_i16() {
    for i in i16::MIN..=i16::MAX {
        let buf = write_leb128(i);
        let (i_decode, _): (i16, _) = buf
            .as_slice()
            .read_leb128()
            .expect("valid i16 should be possible to decode");
        assert_eq!(i, i_decode, "\nLEB128 bytes: {:?}", buf);
    }
}

// Exhaustively test that our encoding is equal to the one from gimli.rs leb128 crate for 16-bit ints.

#[test]
fn same_encodings_as_gimli_u16() {
    for u in u16::MIN..=u16::MAX {
        let our_buf = write_leb128(u);
        let mut gimli_buf = Vec::new();
        gimli_leb128::write::unsigned(&mut gimli_buf, u as u64).unwrap();
        assert_eq!(our_buf, gimli_buf, "\nu: {}", u);
    }
}

#[test]
fn same_encodings_as_gimli_i16() {
    for i in i16::MIN..=i16::MAX {
        let our_buf = write_leb128(i);
        let mut gimli_buf = Vec::new();
        gimli_leb128::write::signed(&mut gimli_buf, i as i64).unwrap();
        assert_eq!(our_buf, gimli_buf, "\ni: {}", i);
    }
}

// Check for the existence of errors when parsing a LEB128 value that doesn't fit in the target type.

/// Utility macro to check for overflow errors when converting from a wider to a narrower type.
macro_rules! detect_overflow {
    ($original_value: expr, $T: ty, $U: ty) => ({
        // Encode as the wider type.
        let original_value: $T = $original_value;
        let buf = write_leb128(original_value);

        // Decode as the narrower type.
        let decoded_value: Result<($U, _), _> = buf.as_slice().read_leb128();

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
            assert_eq!(original_value, decoded_value.unwrap().0 as $T);
        }
    })
}

#[test]
fn overflow_is_detected_some_i32_to_i16() {
    // We cannot exhaustively test all 32-bit numbers, so let's pick some special values:
    let values = [
        // Those two overflow because they use more bytes than possible for an i16 (5 instead of max 3).
        i32::MIN,
        i32::MIN + 1,
        // Should overflow because even though it encodes to 3 bytes only, the high bits of the
        // last byte are too large to be representable in an i16.
        i16::MIN as i32 - 1,
        // Next seven should NOT overflow, they are valid i16s as well.
        i16::MIN as i32,
        i16::MIN as i32 + 1,
        -1,
        0,
        1,
        i16::MAX as i32 - 1,
        i16::MAX as i32,
        // Overflow because of high bits in last byte.
        i16::MAX as i32 + 1,
        // Overflow because too many bytes for i16 LEB128 (5 instead of 3).
        i32::MAX - 1,
        i32::MAX,
    ];

    for &i in &values {
        detect_overflow!(i, i32, i16)
    }
}

#[test]
fn overflow_is_detected_some_u32_to_u16() {
    // Similar to the test case above, just without the negative numbers.
    let values = [
        0,
        1,
        u16::MAX as u32 - 1,
        u16::MAX as u32,
        u16::MAX as u32 + 1,
        u32::MAX - 1,
        u32::MAX,
    ];

    for &u in &values {
        detect_overflow!(u, u32, u16)
    }
}

#[test]
fn overflow_is_detected_all_i16_to_i8() {
    // For 16-bit values, we can test overflow detection exhaustively.
    for i in i16::MIN..=i16::MAX {
        detect_overflow!(i, i16, i8)
    }
}

#[test]
fn overflow_is_detected_all_u16_to_u8() {
    // Same as above, just for all unsigned 16-bit integers.
    for u in u16::MIN..=u16::MAX {
        detect_overflow!(u, u16, u8)
    }
}
