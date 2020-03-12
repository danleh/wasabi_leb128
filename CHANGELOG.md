This document lists the largest (in particular, breaking) changes between versions.

# 0.4.0

- Breaking change: `read_leb128()` now also returns the number of bytes consumed from the reader.

# 0.3.0

- First public version.
- Renamed crate to `wasabi_leb128` to disambiguate against gimli.rs `leb128` crate.
- Add `ParseLeb128Error` type instead of piggy-backing on `io::Error`.

# Before

- No changelog kept.

