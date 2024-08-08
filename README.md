# i48: A 48-bit Signed Integer Type for Rust

`i48` provides a 48-bit signed integer type for Rust, filling the gap between `i32` and `i64`.
This type may be useful in certain scenarios where 48-bit precision is required but 64 bits would be excessive.

## Features

- Efficient 48-bit signed integer representation
- Seamless conversion to and from `i64`
- Support for basic arithmetic operations with overflow checking
- Bitwise operations
- Conversions from various byte representations (little-endian, big-endian, native)
- Implements common traits like `Debug`, `Display`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, and `Hash`

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
i48 = "1.1.0"
```

## Usage

```rust
use i48::i48;

let a: i48 = 1000.into();
let b: i48 = 2000.into();
let c = a + b;

assert_eq!(c.to_i64(), 3000);
```

## Safety and Limitations

- The valid range for `i48` is [-140,737,488,355,328; 140,737,488,355,327].
- Overflow behavior in arithmetic operations matches that of `i64`.
- Bitwise operations are performed on the 48-bit representation.

Always use checked arithmetic operations when dealing with untrusted input or when overflow/underflow is a concern.

## Optional Features

- **pyo3**: Enables PyO3 bindings for use in Python.

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request. This project needs more testing and verification.

## License

This project is licensed under the MIT License - see the [LICENSE](https://github.com/Chubercik/i48/blob/main/LICENSE) file for details.

## Related Projects

This crate came about as a twin project to the [`i24` crate](https://crates.io/crates/i24), one that supports 48-bit signed integers.

Also, check out:

- [`ux` crate](https://crates.io/crates/ux), which provides `u1`-`u127` and `i1`-`i127` types that should behave as similar as possible to the built in rust types,
- [`intx` crate](https://crates.io/crates/intx), which provides new integer types with non-standard and fixed bitwidths (such as `u24`, `i48`, `u96`, etc.).
