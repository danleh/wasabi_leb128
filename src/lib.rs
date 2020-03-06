//! Read and write the variable length [LEB128](https://en.wikipedia.org/wiki/LEB128) number format.
//!
//! LEB128 ("Little Endian Base 128") is used, for example in [DWARF debugging information](http://dwarfstd.org/doc/dwarf-2.0.0.pdf)
//! (see Appenix 4 for C pseudo code) and in the [WebAssembly binary format](https://webassembly.github.io/spec/core/binary/values.html).
//!
//! # Example
//!
//! ```
//! use wasabi_leb128::{ReadLeb128, WriteLeb128};
//!
//! // Vec<u8> as byte-oriented reader/writer.
//! let mut buf = Vec::new();
//!
//! // Encoding/writing a u16 as an LEB128 byte sequence.
//! let original_value: u16 = 128;
//! buf.write_leb128(original_value).unwrap();
//! assert_eq!(buf, [0x80, 0x01]);
//!
//! // Decoding/reading an LEB128 number back to a u16.
//! let (value, bytes_read): (u16, usize) = buf.as_slice().read_leb128().unwrap();
//! assert_eq!(value, original_value);
//! ```
//!
//! See [`ReadLeb128`] and [`WriteLeb128`] traits for more information.
//!
//! # Related Work
//!
//! Other open-source implementations of LEB128 numbers:
//! * LLVM: <http://llvm.org/doxygen/LEB128_8h_source.html>
//!     * Note that `decodesSLEB128()` seems to have no overflow checking!?
//! * V8: <https://github.com/v8/v8/blob/4b9b23521e6fd42373ebbcb20ebe03bf445494f9/src/wasm/decoder.h#L329>
//!     * Note some clever engineering: template-based unrolling, handling of signed and unsigned
//!   and different sizes in a single template, proper overflow checks.
//! * `parity-wasm` crate: <https://github.com/paritytech/parity-wasm/blob/556a02a6d2e816044d2e486bf78123a9bc0657f5/src/elements/primitives.rs#L35>
//! * `leb128` crate: <https://github.com/gimli-rs/leb128>
//!
//! Differences between this crate and existing Rust implementations in `parity-wasm` and `leb128`:
//! - Available for all primitive integers (not just `u64` or `i64`).
//! - A single, combined implementation for signed/unsigned and all sizes (thanks to `num_traits`).
//! - Proper overflow checking for all target types when parsing.
//! - (Hopefully:) easy to understand, comments and explanations inline.

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

/// A trait that extends readers (implementers of the [`io::Read`] trait) with a method to parse
/// LEB128 encoded primitive integers.
pub trait ReadLeb128<T>: io::Read {
    /// Reads an LEB128 encoded integer of type `T` by decoding a sequence of bytes from `self`.
    ///
    /// If successful, it returns the parsed value and the number of bytes consumed from `self`,
    /// otherwise a [`ParseLeb128Error`].
    ///
    /// # Example
    ///
    /// ```
    /// use wasabi_leb128::ReadLeb128;
    ///
    /// // Wrap the array in an io::Cursor, which implements io::Read.
    /// let mut buf = std::io::Cursor::new([0x80, 0x01]);
    /// let (value, bytes_read): (u8, usize) = buf.read_leb128().unwrap();
    /// assert_eq!(value, 128);
    /// assert_eq!(bytes_read, 2);
    /// ```
    fn read_leb128(&mut self) -> Result<(T, usize), ParseLeb128Error>;
}

/// A trait that extends writers (implementers of the [`io::Write`] trait) with a method to write
/// LEB128 encodings of primitive integers.
pub trait WriteLeb128<T>: io::Write {
    /// Writes a primitive integer `value` as a variable-length LEB128 byte sequence into `self`.
    ///
    /// If successful, it returns the number of bytes written to `self`, i.e., the length of the
    /// LEB128 encoding of `value`.
    ///
    /// Note that there is no specific error type (just the regular [`io::Error`] of the writer)
    /// for encoding integers to LEB128, because all primitive integer values can always be
    /// represented as a (wide enough) LEB128 byte sequence.
    ///
    /// # Example
    ///
    /// ```
    /// use wasabi_leb128::WriteLeb128;
    ///
    /// // Vec<u8> implements io::Write.
    /// let mut buf = Vec::new();
    /// let bytes_written = buf.write_leb128(128u8).unwrap();
    /// assert_eq!(buf, [0x80, 0x01]);
    /// assert_eq!(bytes_written, 2);
    /// ```
    fn write_leb128(&mut self, value: T) -> io::Result<usize>;
}

/// Errors while parsing an LEB128 value from an [`io::Read`] reader.
#[derive(Debug)]
pub enum ParseLeb128Error {
    /// The input LEB128 value is larger than can be represented in the target type, because the
    /// input had too many bytes (i.e., more bytes than [`max_bytes::<T>()`](max_bytes)).
    OverflowTooManyBytes,
    /// The input LEB128 value is larger than can be represented in the target type, because the
    /// last byte of the LEB128 sequence contains invalid extra bits.
    OverflowExtraBits,
    /// The input ended before a full LEB128 value could be parsed.
    /// The unnamed argument is the underlying [`io::Error`].
    UnexpectedEndOfData(io::Error),
    /// Any other [`io::Error`] during reading that is not specific to parsing LEB128 values.
    Other(io::Error),
}

/// Maximum number of bytes that the LEB128 encoding of values of type `T` can take.
///
/// For example:
/// ```
/// assert_eq!(wasabi_leb128::max_bytes::<u8>(), 2);
/// assert_eq!(wasabi_leb128::max_bytes::<i32>(), 5);
/// assert_eq!(wasabi_leb128::max_bytes::<u64>(), 10);
/// ```
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
            ParseLeb128Error::OverflowTooManyBytes => {
                "overflow while parsing LEB128 number, too many bytes"
            }
            ParseLeb128Error::OverflowExtraBits => {
                "overflow while parsing LEB128 number, invalid extra bits in last byte"
            }
            ParseLeb128Error::UnexpectedEndOfData(_) => {
                "input data ended before parsed LEB128 number was complete"
            }
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

/// Combined implementation for reading LEB128 to signed and unsigned primitive integers.
impl<R, T> ReadLeb128<T> for R
where
    R: io::Read,
    T: PrimInt + 'static,
    u8: AsPrimitive<T>,
{
    fn read_leb128(&mut self) -> Result<(T, usize), ParseLeb128Error> {
        // TODO Should be const, not let because it only depends on T, but Rust doesn't allow it (yet).
        // Rust 1.37: "error[E0401]: can't use generic parameters from outer function".
        let bits: usize = std::mem::size_of::<T>() * 8;

        let mut value = T::zero();
        let mut shift: usize = 0;
        let mut bytes_read = 0;
        let mut current_byte = CONTINUATION_BIT;

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

            if bytes_read > max_bytes::<T>() {
                return Err(ParseLeb128Error::OverflowTooManyBytes);
            }

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
                let value_bit_count: usize = bits
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

        Ok((value, bytes_read))
    }
}

/// Combined implementation for writing signed and unsigned primitive integers as LEB128.
impl<W, T> WriteLeb128<T> for W
where
    W: io::Write,
    T: PrimInt,
    T: AsPrimitive<u8>,
{
    fn write_leb128(&mut self, mut value: T) -> io::Result<usize> {
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
//   Returns the number of read bytes (i.e., the length of the original encoding) alongside the value itself.
// - write_leb128_with_size(&mut self, mut value: T, min_bytes: usize):
//   Write at least min_bytes LEB128 encoding of T. E.g., for compressed numbers to be back-patchable.
