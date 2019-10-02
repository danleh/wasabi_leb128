# wasabi_leb128 [![build status](https://travis-ci.com/danleh/wasabi_leb128.svg?branch=master)](https://travis-ci.com/danleh/wasabi_leb128)

Read and write the variable length [LEB128](https://en.wikipedia.org/wiki/LEB128) number format. For example:

```Rust
use wasabi_leb128::{ReadLeb128, WriteLeb128};

// Vec<u8> as byte-oriented reader/writer.
let mut buf = Vec::new();

// Encoding/writing a u16 as an LEB128 byte sequence.
let original_value: u16 = 128;
buf.write_leb128(original_value).unwrap();
assert_eq!(buf, [0x80, 0x01]);

// Decoding/reading an LEB128 number back to a u16.
let value: u16 = buf.as_slice().read_leb128().unwrap();
assert_eq!(value, original_value);
```

For more info, see: 
- [Package information](https://crates.io/crates/wasabi_leb128) on crates.io
- [Documentation](https://docs.rs/wasabi_leb128/) on Docs.rs
