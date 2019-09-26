use std::error;
use std::fmt;
use std::io;

use byteorder::ReadBytesExt;
use num_traits::*;

#[cfg(test)]
mod tests;

/* Traits for encoding and decoding Leb128 primitive integers */

pub trait ReadLeb128<T>: io::Read {
    fn read_leb128(&mut self) -> io::Result<T>;
}

pub trait WriteLeb128<T>: io::Write {
    /// Returns the actual written byte count.
    fn write_leb128(&mut self, value: T) -> Result<usize, Leb128Error>;
}

#[derive(Debug)]
pub enum Leb128Error {
    Overflow,
    UnexpectedEof(io::Error),
    Other(io::Error),
}

impl fmt::Display for Leb128Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        unimplemented!() // FIXME
    }
}

impl error::Error for Leb128Error {}

impl From<io::Error> for Leb128Error {
    fn from(e: io::Error) -> Self {
        match e.kind() {
            // TODO better error message, more data?
            io::ErrorKind::UnexpectedEof => Leb128Error::UnexpectedEof(e),
            _ => Leb128Error::Other(e),
        }
    }
}

/* Trait implementations */

const CONTINUATION_BIT: u8 = 0x80;

#[inline]
fn continuation_bit(byte: u8) -> bool {
    byte & CONTINUATION_BIT == CONTINUATION_BIT
}

const SIGN_BIT: u8 = 0x40;

#[inline]
fn sign_bit(byte: u8) -> bool {
    byte & SIGN_BIT == SIGN_BIT
}

macro_rules! signed {
    ($T: ident) => {
        $T::min_value() != 0
    };
}

// For inspiration, see
// Wiki: https://en.wikipedia.org/wiki/LEB128
// Official DWARF spec, annex C: http://dwarfstd.org/doc/dwarf-2.0.0.pdf
// LLVM implementation: http://llvm.org/doxygen/LEB128_8h_source.html
//      NOTE decodesSLEB128 seems to have no overflow checking!?
//      Only 128bits?
// V8 implementation: https://github.com/v8/v8/blob/4b9b23521e6fd42373ebbcb20ebe03bf445494f9/src/wasm/decoder.h#L329
//      NOTE the template-based unrolling!
//      Signed and unsigned, and different sizes in one function template
// parity-wasm implementation: https://github.com/paritytech/parity-wasm/blob/master/src/elements/primitives.rs#L35
// leb128 crate: https://github.com/gimli-rs/leb128
// WebAssembly spec (for signed vs. unsigned vs. "uninterpreted"): https://webassembly.github.io/spec/core/binary/values.html
// About shift overflow detection: https://blogs.msdn.microsoft.com/xiangfan/2009/06/13/detect-shift-overflow/

// Need to write this as a macro, not a generic impl because num_traits are quite lacking, e.g.,
// there is no "U as T" for primitive integers.
// TODO can this be written without a macro?
macro_rules! impl_leb128_integer {
    ($T: ident) => {
        impl<R: io::Read> ReadLeb128<$T> for R {
            fn read_leb128(&mut self) -> io::Result<$T> {
                let mut value = 0;
                // useful if you want to preserve length when encoding this LEB128 again (unused currently though)
                let mut _bytes_read = 0;
                let mut shift = 0;
                let mut byte = CONTINUATION_BIT;


                const T_size_bits: usize = std::mem::size_of::<$T>() * 8;
                // see https://stackoverflow.com/questions/2745074/fast-ceiling-of-an-integer-division-in-c-c
                const fn int_div_ceil(x: usize, y: usize) -> usize {
                    x/y + (x % y != 0) as usize
                }
                const T_max_leb128_bytes: usize = int_div_ceil(T_size_bits, 7);
//                println!("\nT: {}\nT_size_bits: {}\nT_max_leb128_bytes: {}\n", stringify!($T), T_size_bits, T_max_leb128_bytes);


                while continuation_bit(byte) {
                    // TODO better error message if ErrorKind::UnexpectedEof -> LEB128 unexpected end
                    byte = self.read_u8().map_err(|e| io::Error::new(
                                io::ErrorKind::InvalidData,
                                format!("unexpected end of LEB128 data after {} bytes read, current value: {}\ncaused by:{}", _bytes_read, value, e)))?;

                    // mask off continuation bit from byte and prepend lower 7 bits to value
                    // FIXME checked_shl does actually NOT check for overflow of the shifted value,
                    // only that the shift-number is smaller than the number of bits of the target type
                    // NOTE x86 masks off shift > N bits!
                    let low_bits = (byte & !CONTINUATION_BIT) as $T;

                    // TODO add warning for overflow of shift bits


                    let current_byte = shift as usize / 7;
                    let is_last_byte = current_byte == T_max_leb128_bytes - 1;

//                    println!("byte {:x}\ncurrent_byte {}\nis_last_byte {}", byte, current_byte, is_last_byte);

//                    use num_traits::PrimInt;
//                    let overflow = is_last_byte && ((low_bits.wrapping_shl(shift)).wrapping_shr(shift)) != low_bits;
                    let overflow = current_byte > T_max_leb128_bytes;

                    if !overflow {
                        value |= low_bits.wrapping_shl(shift);
//                        println!("shift {}\nlow_bits {:x}\n<<    {:x}\n<< >> {:x}\nvalue {:x}\n", shift, low_bits, low_bits.wrapping_shl(shift), low_bits.wrapping_shl(shift).wrapping_shr(shift), value);
                    } else {
                        return Err(io::Error::new(io::ErrorKind::InvalidData, format!("LEB128 to {} overflow", stringify!($T))));
                    }
                    _bytes_read += 1;
                    shift += 7;
                }

                if signed!($T) {
                    let (sign_extend, did_overflow) = (!0 as $T).overflowing_shl(shift);
                    if sign_bit(byte) && !did_overflow {
//                    let sign_extend = (!0 as $T).wrapping_shl(shift-7+1);
//                    if is_set_sign_bit(byte) {
                        value |= sign_extend;
                    }

//                    println!("extension bits {:x}, shift {}\nsign extended {:x}", sign_extend, shift, value);
                }


                Ok(value)
            }
        }

    }
}

/// Mask off the continuation bit from the byte (= extract only the last 7, meaningful LEB128 bits).
#[inline]
fn non_continuation_bits(byte: u8) -> u8 {
    byte & !CONTINUATION_BIT
}

// Combined implementation for signed and unsigned primitive integers.
impl<W, T> WriteLeb128<T> for W
where
    W: io::Write,
    T: PrimInt + AsPrimitive<u8>,
{
    fn write_leb128(&mut self, mut value: T) -> Result<usize, Leb128Error> {
        let is_negative = value < T::zero();
        let empty_value = if is_negative { !T::zero() } else { T::zero() };

        let mut bytes_written = 0;
        let mut more_bytes = true;

        while more_bytes {
            let mut byte_to_write = non_continuation_bits(value.as_());
            // Shr sign-extends for signed types and is logical shift for unsigned types.
            value = value.shr(7);

            more_bytes = value != empty_value;
            if more_bytes {
                byte_to_write |= CONTINUATION_BIT;
            }

            self.write_all(&[byte_to_write])?;
            bytes_written += 1;
        }

        Ok(bytes_written)
    }
}

impl_leb128_integer!(u32);
impl_leb128_integer!(u64);
impl_leb128_integer!(usize);
impl_leb128_integer!(i32);
impl_leb128_integer!(i64);
impl_leb128_integer!(isize);

// for testing, can be exhaustively checked for correctness
impl_leb128_integer!(u16);
impl_leb128_integer!(i16);
