use std::error;
use std::fmt;
use std::io;

use num_traits::*;


#[cfg(test)]
mod tests;


/* Public API of this crate:
 * - Traits for encoding and decoding types to/from LEB128.
 * - Custom error type (for errors during parsing LEB128 bytes to Rust types).
 * - const fn max_bytes<T>().
 */

pub trait ReadLeb128<T>: io::Read {
    fn read_leb128(&mut self) -> Result<T, ParseLeb128Error>;
}

pub trait WriteLeb128<T>: io::Write {
    /// Returns the number of written bytes, i.e., the length of the LEB128 encoding of value.
    fn write_leb128(&mut self, value: T) -> io::Result<usize>;
}

#[derive(Debug)]
pub enum ParseLeb128Error {
    OverflowTooManyBytes,
    OverflowExtraBits,
    UnexpectedEndOfData(io::Error),
    Other(io::Error),
}

/// Maximum number of bytes of the LEB128 encoding for values of type T.
pub const fn max_bytes<T>() -> usize {
    // See https://stackoverflow.com/questions/2745074/fast-ceiling-of-an-integer-division-in-c-c
    const fn int_div_ceil(x: usize, y: usize) -> usize {
        1 + ((x - 1) / y)
    }

    // ceil( bits(T) / 7 non-continuation bits per LEB128 byte )
    int_div_ceil(std::mem::size_of::<T>() * 8, 7)
}


/* Implementation of the error type. */

impl fmt::Display for ParseLeb128Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let s = match self {
            ParseLeb128Error::OverflowTooManyBytes => "invalid LEB128, had too many bytes",
            ParseLeb128Error::OverflowExtraBits => "invalid LEB128, invalid extra bits in last byte",
            ParseLeb128Error::UnexpectedEndOfData(_) => "invalid LEB128, input data ended before parsing full number",
            ParseLeb128Error::Other(_) => "other error",
        };
        f.write_str(s)
    }
}

impl error::Error for ParseLeb128Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            ParseLeb128Error::UnexpectedEndOfData(e) | ParseLeb128Error::Other(e) => Some(e),
            _ => None,
        }
    }
}

impl From<io::Error> for ParseLeb128Error {
    fn from(e: io::Error) -> Self {
        ParseLeb128Error::Other(e)
    }
}


/* Helper functions and constants for clarity. */

/// Checks whether a primitive integer type is signed (not available in num_traits, unfortunately.)
// TODO This should be a const fn, but it's not possible (yet, let's track const fn progress...).
// Rust 1.37: "error[E0723]: trait bounds other than `Sized` on const fn parameters are unstable".
fn is_signed<T: PrimInt>() -> bool {
    !T::min_value().is_zero()
}

const CONTINUATION_BIT: u8 = 0x80;

#[inline]
fn continuation_bit(byte: u8) -> bool {
    byte & CONTINUATION_BIT == CONTINUATION_BIT
}

/// Mask off the continuation bit from the byte (= extract only the last 7, meaningful LEB128 bits).
#[inline]
fn non_continuation_bits(byte: u8) -> u8 {
    byte & !CONTINUATION_BIT
}

const SIGN_BIT: u8 = 0x40;

#[inline]
fn sign_bit(byte: u8) -> bool {
    byte & SIGN_BIT == SIGN_BIT
}


/* Trait implementation for all primitive integer types. */

// For more information about the LEB128 format, see:
// - Wikipedia: https://en.wikipedia.org/wiki/LEB128
// - Official DWARF specification, Appendix 4: http://dwarfstd.org/doc/dwarf-2.0.0.pdf
// - LLVM implementation: http://llvm.org/doxygen/LEB128_8h_source.html
//   NOTE decodesSLEB128 seems to have no overflow checking!?
// - V8 implementation: https://github.com/v8/v8/blob/4b9b23521e6fd42373ebbcb20ebe03bf445494f9/src/wasm/decoder.h#L329
//   NOTE template-based unrolling, handling of signed and unsigned and different sizes in a single
//   template, proper overflow checks.
// - parity-wasm implementation: https://github.com/paritytech/parity-wasm/blob/master/src/elements/primitives.rs#L35
// - leb128 crate: https://github.com/gimli-rs/leb128
// - WebAssembly spec (for signed vs. unsigned vs. "uninterpreted"): https://webassembly.github.io/spec/core/binary/values.html

impl<R, T> ReadLeb128<T> for R
where
    R: io::Read,
    T: PrimInt + 'static,
    u8: AsPrimitive<T>,
{
    fn read_leb128(&mut self) -> Result<T, ParseLeb128Error> {
        // TODO Should be const, not let because it only depends on T, but Rust doesn't allow it (yet).
        // Rust 1.37: "error[E0401]: can't use generic parameters from outer function".
        let bits = std::mem::size_of::<T>() * 8;

        let mut value = T::zero();
        let mut shift: usize = 0;
        let mut bytes_read = 0;
        let mut current_byte = CONTINUATION_BIT;

        //        for bytes_read in 0..max_bytes::<T>() {
        //            current_byte = {
        //                let mut buf = [0u8];
        //                self.read_exact(&mut buf)/*.map_err(|e| match e.kind() {
        //                    // Return custom error if input bytes end before full LEB128 could be parsed.
        //                    io::ErrorKind::UnexpectedEof => ParseLeb128Error::UnexpectedEndOfData(e),
        //                    _ => ParseLeb128Error::Other(e),
        //                })*/?;
        //                buf[0]
        //            };
        //
        //            let is_last_byte = bytes_read == max_bytes::<T>() - 1;
        //            if is_last_byte {
        //                if continuation_bit(current_byte) {
        //                    return Err(ParseLeb128Error::OverflowTooManyBytes);
        //                }
        //
        //                let value_bit_count = bits
        //                    // Bits in the LEB128 bytes so far.
        //                    - ((max_bytes::<T>() - 1) * 7)
        //                    // For signed values, we also check the sign bit, so there is one less value bit.
        //                    - if is_signed::<T>() { 1 } else { 0 };
        //                // Extract the extra bits and the sign bit (for signed values) from the input byte.
        //                let extra_bits_mask = non_continuation_bits(0xffu8 << value_bit_count);
        //                let extra_bits = current_byte & extra_bits_mask;
        //
        //                let extra_bits_empty = if is_signed::<T>() {
        //                    // All 0 (positive value) or all 1 (negative value, properly sign-extended).
        //                    extra_bits == 0 || extra_bits == extra_bits_mask
        //                } else {
        //                    extra_bits == 0
        //                };
        //
        //                if !extra_bits_empty {
        //                    return Err(ParseLeb128Error::OverflowExtraBits);
        //                }
        //            }
        //
        //            // Prepend the extracted bits to value.
        //            // The following shift left cannot overflow (= shift amount larger than target type,
        //            // which would be an error in Rust), because the previous condition implies it already:
        //            //     bytes_read <= max_bytes(T)      // condition that is ensured above
        //            // <=> bytes_read <= ceil(bits(T) / 7) // substitute definition of max_bytes
        //            // <=> bytes_read < bits(T) / 7 + 1    // forall x: ceil(x) < x + 1, here x = bits(T) / 7
        //            // <=> shift / 7 + 1 < bits(T) / 7 + 1 // express bytes_read in terms of shift
        //            // <=> shift < bits(T)                 // qed.
        //            let new_bits: T = non_continuation_bits(current_byte).as_().shl(shift);
        //            value = value.bitor(new_bits);
        //
        //            shift += 7;
        //
        //            if !continuation_bit(current_byte) {
        //                break;
        //            }
        //        }

        while continuation_bit(current_byte) {
            current_byte = {
                let mut buf = [0u8];
                self.read_exact(&mut buf).map_err(|e| match e.kind() {
                    // Return custom error if input bytes end before full LEB128 could be parsed.
                    io::ErrorKind::UnexpectedEof => ParseLeb128Error::UnexpectedEndOfData(e),
                    _ => ParseLeb128Error::Other(e),
                })?;
                buf[0]
            };
            bytes_read += 1;

            // if shift >= bits { // same thing, but without using bytes_read
            if bytes_read > max_bytes::<T>() {
                return Err(ParseLeb128Error::OverflowTooManyBytes);
            }

            // let is_last_byte = shift == (max_bytes::<T>() - 1)*7; // same
            let is_last_byte = bytes_read == max_bytes::<T>();
            if is_last_byte {
                // The last LEB128 byte has the following structure:
                // -------------------------
                // | c | u ... | s | v ... |
                // -------------------------
                // Where:
                // - c = continuation bit.
                // - u = undefined or "extra bits", which cannot be represented in the target type.
                // - s = sign bit (only if target type is signed).
                // - v = the remaining "value bits".
                // We need to check that:
                // - For signed types: all u bits are equal to the sign bit s. (The byte must be
                //   properly sign-extended.)
                // - For unsigned types: all u bits are 0. (There is no sign bit s.)

                // TODO This should be const (depends on T only), but doesn't work yet, see above.
                let value_bit_count = bits
                    // Bits in the LEB128 bytes so far.
                    - ((max_bytes::<T>() - 1) * 7)
                    // For signed values, we also check the sign bit, so there is one less value bit.
                    - if is_signed::<T>() { 1 } else { 0 };
                // Extract the extra bits and the sign bit (for signed values) from the input byte.
                let extra_bits_mask = non_continuation_bits(0xffu8 << value_bit_count);
                let extra_bits = current_byte & extra_bits_mask;

                let extra_bits_valid = if is_signed::<T>() {
                    // For signed types: The extra bits *plus* the sign bit must either be all 0
                    // (non-negative value) or all 1 (negative value, properly sign-extended).
                    extra_bits == 0 || extra_bits == extra_bits_mask
                } else {
                    // For unsigned types: extra bits must be 0.
                    extra_bits == 0
                };

                if !extra_bits_valid {
                    return Err(ParseLeb128Error::OverflowExtraBits);
                }
            }

            // Prepend the extracted bits to value.
            // The following shift left cannot overflow (= shift amount larger than target type,
            // which would be an error in Rust), because the previous condition implies it already:
            //     bytes_read <= max_bytes(T)      // condition that is ensured above
            // <=> bytes_read <= ceil(bits(T) / 7) // substitute definition of max_bytes
            // <=> bytes_read < bits(T) / 7 + 1    // forall x: ceil(x) < x + 1, here x = bits(T) / 7
            // <=> shift / 7 + 1 < bits(T) / 7 + 1 // express bytes_read in terms of shift
            // <=> shift < bits(T)                 // qed.
            let new_bits: T = non_continuation_bits(current_byte).as_().shl(shift);
            value = value.bitor(new_bits);

            shift += 7;
        }

        // Sign-extend value if:
        // - type is signed
        if is_signed::<T>()
            // - value is negative (= sign bit of last LEB128 byte was set)
            && sign_bit(current_byte)
            // - shift amount does not overflow bit-width of target type
            //   (disallowed in Rust, will panic in debug mode).
            && shift < bits
        {
            let sign_extend = (!T::zero()).shl(shift);
            value = value.bitor(sign_extend);
        }

        Ok(value)
    }
}

// Combined implementation for signed and unsigned primitive integers.
impl<W, T> WriteLeb128<T> for W
where
    W: io::Write,
    T: PrimInt,
    T: AsPrimitive<u8>,
{
    fn write_leb128(&mut self, mut value: T) -> Result<usize, io::Error> {
        let mut bytes_written = 0;
        let mut more_bytes = true;

        while more_bytes {
            let mut byte_to_write = non_continuation_bits(value.as_());
            // Shr sign-extends for signed types and is logical shift for unsigned types.
            value = value.shr(7);

            let done = if is_signed::<T>() {
                // For signed values:
                if sign_bit(byte_to_write) {
                    // If the MSB of the last written byte is set (= the "sign bit") AND
                    // if remaining value is all 1's (= they are all copies of the sign bit) -> DONE.
                    value == !T::zero()
                } else {
                    // If the MSB of the last written byte is not set:
                    // then we are done if no more other bits are remaining in value.
                    value == T::zero()
                }
            } else {
                // For unsigned values: if value == 0, then we wrote all of its bits.
                value == T::zero()
            };
            more_bytes = !done;
            if more_bytes {
                byte_to_write |= CONTINUATION_BIT;
            }

            self.write_all(&[byte_to_write])?;
            bytes_written += 1;
        }

        Ok(bytes_written)
    }
}

// TODO Add trait methods:
// - read_leb128_with_size(&mut self) -> Result<(T, usize), Error>:
//   Returns the number of read bytes (i.e., the length of the encoding) alongside the value itself.
// - write_leb128_with_size(&mut self, mut value: T, min_bytes: usize):
//   Write at least min_bytes LEB128 encoding of T. E.g., for compressed numbers to be back-patchable.
