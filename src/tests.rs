use crate::{ReadLeb128, WriteLeb128};

use std::io;
use std::{i16, i32, u16};
use std::convert::TryFrom;

// Utility function that gives back a vector of bytes with the LEB128 representation of x.
fn write_leb128<T>(x: T) -> Vec<u8>
where
    Vec<u8>: WriteLeb128<T>,
{
    let mut buf = Vec::new();
    buf.write_leb128(x).expect("writing to a vector should never fail, since all input values can be represented in LEB128");
    buf
}

#[test]
fn known_values() {
    // Unsigned numbers:
    assert_eq!(write_leb128(0_u32), [0x00]);
    assert_eq!(write_leb128(1_u32), [0x01]);
    assert_eq!(write_leb128(127_u32), [0x7f]);
    assert_eq!(write_leb128(128_u32), [0x80, 0x01]);
    assert_eq!(write_leb128(16256_u32), [0x80, 0x7f]);

    // Signed numbers:
    assert_eq!(write_leb128(0_i32), [0x00]);
    assert_eq!(write_leb128(1_i32), [0x01]);
    assert_eq!(write_leb128(-1_i32), [0x7f]);
    assert_eq!(write_leb128(127_i32), [0xff, 0x00]);
    assert_eq!(write_leb128(-127_i32), [0x81, 0x7f]);
    assert_eq!(write_leb128(128_i32), [0x80, 0x01]);
    assert_eq!(write_leb128(-128_i32), [0x80, 0x7f]);
}

#[test]
/// Exhaustively test that decode(encode(value)) == value for u16 and i16.
fn roundtrips() -> Result<(), io::Error> {
    for u in u16::MIN..=u16::MAX {
        let buf = write_leb128(u);
        let u_decode: u16 = buf.as_slice().read_leb128()?;

        assert_eq!(u, u_decode, "\nLEB128 bytes: {:?}", buf);
    }

    for i in i16::MIN..=i16::MAX {
        let buf = write_leb128(i);
        let i_decode: i16 = buf.as_slice().read_leb128()?;

        assert_eq!(i, i_decode, "\nLEB128 bytes: {:?}", buf);
    }

    Ok(())
}

#[test]
fn overflow_is_detected() -> Result<(), std::io::Error> {
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

    for &i_original in &values {
        // Encode as 32 bit.
        let buf = write_leb128(i_original);

        // Decode as 16 bit.
        let i_decode: Result<i16, _> = buf.as_slice().read_leb128();

        // If the input value cannot be represented without loss in the target type,
        // read_leb128() should have Err()'d.
        let overflow = i16::try_from(i_original).is_err();
        if overflow {
            assert!(
                i_decode.is_err(),
                "expected overflow when decoding i32 {} ({:?} in LEB128) as i16, but got {:?}",
                i_original,
                buf,
                i_decode
            );
        } else {
            assert_eq!(i_original, i_decode? as i32);
        }
    }

    Ok(())
}
