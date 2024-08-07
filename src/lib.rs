//! # i48: A 48-bit Signed Integer Type
//!
//! The `i48` crate provides a 48-bit signed integer type for Rust, filling the gap between
//! `i32` and `i64`. This type is particularly useful in image processing (deep color)
//! and other scenarios where 48-bit precision is required but 64 bits would be excessive.
//!
//! ## Features
//!
//! - Efficient 48-bit signed integer representation
//! - Seamless conversion to and from `i64`
//! - Support for basic arithmetic operations with overflow checking
//! - Bitwise operations
//! - Conversions from various byte representations (little-endian, big-endian, native)
//! - Implements common traits like `Debug`, `Display`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, and `Hash`
//!
//! This crate came about as a twin project to the `[i24](https://crates.io/crates/i24)` crate, one that supports 48-bit signed integers.
//! The `i48` struct also has pyo3 bindings for use in Python. Enable the ``pyo3`` feature to use the pyo3 bindings.
//!
//! ## Usage
//!
//! Add this to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! i48 = "1.0.0"
//! ```
//!
//! Then, in your Rust code:
//!
//! ```rust
//! use i48::i48;
//!
//! let a = i48::from_i64(1000);
//! let b = i48::from_i64(2000);
//! let c = a + b;
//! assert_eq!(c.to_i64(), 3000);
//! ```
//!
//! ## Safety and Limitations
//!
//! While `i48` strives to behave similarly to Rust's built-in integer types, there are some
//! important considerations:
//!
//! - The valid range for `i48` is [−140,737,488,355,328; 140,737,488,355,327].
//! - Overflow behavior in arithmetic operations matches that of `i64`.
//! - Bitwise operations are performed on the 48-bit representation.
//!
//! Always use checked arithmetic operations when dealing with untrusted input or when
//! overflow/underflow is a concern.
//!
//! ## Features
//! - **pyo3**: Enables the pyo3 bindings for the `i48` type.
//!
//! ## Contributing
//!
//! Contributions are welcome! Please feel free to submit a Pull Request. This really needs more testing and verification.
//!
//! ## License
//!
//! This project is licensed under MIT - see the [LICENSE](https://github.com/Chubercik/i48/blob/main/LICENSE) file for details.
//!
use bytemuck::{Pod, Zeroable};
use num_traits::{Num, One, Zero};
use std::fmt;
use std::fmt::Display;
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};
use std::{
    ops::{Neg, Not},
    str::FromStr,
};

#[cfg(feature = "pyo3")]
use pyo3::prelude::*;

/// Represents errors that can occur when working with the `i48` type.
#[derive(Debug, PartialEq, Eq)]
pub enum I48Error {
    /// An error occurred while parsing a string to an `i48`.
    ///
    /// This variant wraps the standard library's `ParseIntError`.
    ParseError(std::num::ParseIntError),

    /// The value is out of the valid range for an `i48`.
    ///
    /// Valid range for `i48` is [−140,737,488,355,328; 140,737,488,355,327].
    OutOfRange,
}

impl std::fmt::Display for I48Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            I48Error::ParseError(e) => write!(f, "Parse error: {}", e),
            I48Error::OutOfRange => write!(f, "Value out of range for i48"),
        }
    }
}

impl std::error::Error for I48Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            I48Error::ParseError(e) => Some(e),
            I48Error::OutOfRange => None,
        }
    }
}

impl From<std::num::ParseIntError> for I48Error {
    fn from(err: std::num::ParseIntError) -> Self {
        I48Error::ParseError(err)
    }
}

#[allow(non_camel_case_types)]
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[cfg_attr(feature = "pyo3", pyclass)]
/// An experimental 48-bit signed integer type.
///
/// This type is a wrapper around ``[u8; 6]`` and is used to represent 48-bit data.
/// It should not be used anywhere important. It is still unverified and experimental.
///
/// The type is not yet fully implemented and is not guaranteed to work.
/// Supports basic arithmetic operations and conversions to and from ``i64``.
///
/// Represents a 48-bit signed integer.
///
/// This struct stores the integer as six bytes in little-endian order.
pub struct i48 {
    /// The raw byte representation of the 48-bit integer.
    pub data: [u8; 6],
}

impl i48 {
    /// Converts the 48-bit integer to a 64-bit signed integer.
    ///
    /// This method performs sign extension if the 48-bit integer is negative.
    ///
    /// # Returns
    ///
    /// The 64-bit signed integer representation of this `i48`.
    pub const fn to_i64(self) -> i64 {
        let [a, b, c, d, e, f] = self.data;
        let value = i64::from_le_bytes([a, b, c, d, e, f, 0, 0]);
        if value & 0x800000000000 != 0 {
            value | 0xFFFF000000000000u64 as i64
        } else {
            value
        }
    }

    /// Creates an `i48` from a 64-bit signed integer.
    ///
    /// This method truncates the input to 48 bits if it's outside the valid range.
    ///
    /// # Arguments
    ///
    /// * `n` - The 64-bit signed integer to convert.
    ///
    /// # Returns
    ///
    /// An `i48` instance representing the input value.
    pub const fn from_i64(n: i64) -> Self {
        let bytes = n.to_le_bytes();
        Self {
            data: [bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5]],
        }
    }

    /// Creates an `i48` from six bytes in native endian order.
    ///
    /// # Arguments
    ///
    /// * `bytes` - An array of 6 bytes representing the 48-bit integer.
    ///
    /// # Returns
    ///
    /// An `i48` instance containing the input bytes.
    pub const fn from_ne_bytes(bytes: [u8; 6]) -> Self {
        Self {
            data: [
                if cfg!(target_endian = "big") {
                    bytes[5]
                } else {
                    bytes[0]
                },
                if cfg!(target_endian = "big") {
                    bytes[4]
                } else {
                    bytes[1]
                },
                if cfg!(target_endian = "big") {
                    bytes[3]
                } else {
                    bytes[2]
                },
                if cfg!(target_endian = "big") {
                    bytes[2]
                } else {
                    bytes[3]
                },
                if cfg!(target_endian = "big") {
                    bytes[1]
                } else {
                    bytes[4]
                },
                if cfg!(target_endian = "big") {
                    bytes[0]
                } else {
                    bytes[5]
                },
            ],
        }
    }

    /// Creates an `i48` from six bytes in **little-endian** order.
    ///
    /// # Arguments
    ///
    /// * `bytes` - An array of 6 bytes representing the 48-bit integer in little-endian order.
    ///
    /// # Returns
    ///
    /// An `i48` instance containing the input bytes.
    pub const fn from_le_bytes(bytes: [u8; 6]) -> Self {
        Self {
            data: [bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5]],
        }
    }

    /// Creates an `i48` from six bytes in big-endian order.
    ///
    /// # Arguments
    ///
    /// * `bytes` - An array of 6 bytes representing the 48-bit integer in big-endian order.
    ///
    /// # Returns
    ///
    /// An `i48` instance with the bytes in little-endian order.
    pub const fn from_be_bytes(bytes: [u8; 6]) -> Self {
        Self {
            data: [bytes[5], bytes[4], bytes[3], bytes[2], bytes[1], bytes[0]],
        }
    }

    /// Performs checked addition.
    ///
    /// # Arguments
    ///
    /// * `other` - The `i48` to add to this value.
    ///
    /// # Returns
    ///
    /// `Some(i48)` if the addition was successful, or `None` if it would overflow.
    pub fn checked_add(self, other: Self) -> Option<Self> {
        self.to_i64()
            .checked_add(other.to_i64())
            .map(Self::from_i64)
    }

    /// Performs checked subtraction.
    ///
    /// # Arguments
    ///
    /// * `other` - The `i48` to subtract from this value.
    ///
    /// # Returns
    ///
    /// `Some(i48)` if the subtraction was successful, or `None` if it would overflow.
    pub fn checked_sub(self, other: Self) -> Option<Self> {
        self.to_i64()
            .checked_sub(other.to_i64())
            .map(Self::from_i64)
    }

    /// Performs checked multiplication.
    ///
    /// # Arguments
    ///
    /// * `other` - The `i48` to multiply with this value.
    ///
    /// # Returns
    ///
    /// `Some(i48)` if the multiplication was successful, or `None` if it would overflow.
    pub fn checked_mul(self, other: Self) -> Option<Self> {
        self.to_i64()
            .checked_mul(other.to_i64())
            .map(Self::from_i64)
    }

    /// Performs checked division.
    ///
    /// # Arguments
    ///
    /// * `other` - The `i48` to divide this value by.
    ///
    /// # Returns
    ///
    /// `Some(i48)` if the division was successful, or `None` if the divisor is zero or if the division would overflow.
    pub fn checked_div(self, other: Self) -> Option<Self> {
        self.to_i64()
            .checked_div(other.to_i64())
            .map(Self::from_i64)
    }
}

unsafe impl Zeroable for i48 {}
unsafe impl Pod for i48 {}

impl One for i48 {
    fn one() -> Self {
        i48::from_i64(1)
    }
}

impl Zero for i48 {
    fn zero() -> Self {
        i48::from_i64(0)
    }

    fn is_zero(&self) -> bool {
        i48::from_i64(0) == *self
    }
}

impl Num for i48 {
    type FromStrRadixErr = I48Error;
    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        let i64_result = i64::from_str_radix(str, radix).map_err(I48Error::ParseError)?;
        if !(-140737488355328..=140737488355327).contains(&i64_result) {
            Err(I48Error::OutOfRange)
        } else {
            Ok(i48::from_i64(i64_result))
        }
    }
}

#[cfg(feature = "pyo3")]
use numpy::Element;

#[cfg(feature = "pyo3")]
unsafe impl Element for i48 {
    const IS_COPY: bool = true;

    fn get_dtype_bound(py: Python<'_>) -> Bound<'_, numpy::PyArrayDescr> {
        numpy::dtype_bound::<i48>(py)
    }
}

impl Add for i48 {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let result = self.to_i64().wrapping_add(other.to_i64());
        Self::from_i64(result)
    }
}

impl Sub for i48 {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let result = self.to_i64().wrapping_sub(other.to_i64());
        Self::from_i64(result)
    }
}

impl Mul for i48 {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let result = self.to_i64().wrapping_mul(other.to_i64());
        Self::from_i64(result)
    }
}

impl Div for i48 {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        let result = self.to_i64().wrapping_div(other.to_i64());
        Self::from_i64(result)
    }
}

impl Rem for i48 {
    type Output = Self;

    fn rem(self, other: Self) -> Self {
        let result = self.to_i64().wrapping_rem(other.to_i64());
        Self::from_i64(result)
    }
}

impl Neg for i48 {
    type Output = Self;

    fn neg(self) -> Self {
        let i64_result = self.to_i64().wrapping_neg();
        i48::from_i64(i64_result)
    }
}

impl Not for i48 {
    type Output = Self;

    fn not(self) -> Self {
        let i64_result = !self.to_i64();
        i48::from_i64(i64_result)
    }
}

impl BitAnd for i48 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        let result = self.to_i64() & rhs.to_i64();
        Self::from_i64(result)
    }
}

impl BitOr for i48 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let result = self.to_i64() | rhs.to_i64();
        Self::from_i64(result)
    }
}

impl BitXor for i48 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let result = self.to_i64() ^ rhs.to_i64();
        Self::from_i64(result)
    }
}

impl Shl<u32> for i48 {
    type Output = Self;

    fn shl(self, rhs: u32) -> Self::Output {
        let result = (self.to_i64() << rhs) & 0x0000FFFFFFFFFFFF;
        if result & 0x800000 != 0 {
            Self::from_i64(result | 0xFFFF000000000000u64 as i64)
        } else {
            Self::from_i64(result)
        }
    }
}

impl Shr<u32> for i48 {
    type Output = Self;

    fn shr(self, rhs: u32) -> Self::Output {
        let value = self.to_i64();
        let result = if value < 0 {
            ((value >> rhs) | (-1 << (48 - rhs))) & 0x0000FFFFFFFFFFFF
        } else {
            (value >> rhs) & 0x0000FFFFFFFFFFFF
        };
        Self::from_i64(result)
    }
}

impl Display for i48 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_i64())
    }
}

impl FromStr for i48 {
    type Err = I48Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let i64_result = i64::from_str(s)?;
        if !(-140737488355328..=140737488355327).contains(&i64_result) {
            Err(I48Error::OutOfRange)
        } else {
            Ok(i48::from_i64(i64_result))
        }
    }
}

macro_rules! implement_ops_assign {
    ($($trait_path:path { $($function_name:ident),* }),*) => {
        $(
            impl $trait_path for i48 {
                $(
                    fn $function_name(&mut self, other: Self){
                        let mut self_i64: i64 = self.to_i64();
                        let other_i64: i64 = other.to_i64();
                        self_i64.$function_name(other_i64);
                    }
                )*
            }
        )*
    };
}

macro_rules! implement_ops_assign_ref {
    ($($trait_path:path { $($function_name:ident),* }),*) => {
        $(
            impl $trait_path for &i48 {
                $(
                    fn $function_name(&mut self, other: Self){
                        let mut self_i64: i64 = self.to_i64();
                        let other_i64: i64 = other.to_i64();
                        self_i64.$function_name(other_i64);
                    }
                )*
            }
        )*
    };
}

implement_ops_assign!(
    AddAssign { add_assign },
    SubAssign { sub_assign },
    MulAssign { mul_assign },
    DivAssign { div_assign },
    RemAssign { rem_assign },
    BitAndAssign { bitand_assign },
    BitOrAssign { bitor_assign },
    BitXorAssign { bitxor_assign },
    ShlAssign { shl_assign },
    ShrAssign { shr_assign }
);

implement_ops_assign_ref!(
    AddAssign { add_assign },
    SubAssign { sub_assign },
    MulAssign { mul_assign },
    DivAssign { div_assign },
    RemAssign { rem_assign },
    BitAndAssign { bitand_assign },
    BitOrAssign { bitor_assign },
    BitXorAssign { bitxor_assign },
    ShlAssign { shl_assign },
    ShrAssign { shr_assign }
);

#[cfg(test)]
mod i48_tests {
    use super::*;

    #[test]
    fn test_arithmetic_operations() {
        let a = i48::from_i64(100);
        let b = i48::from_i64(50);

        assert_eq!((a + b).to_i64(), 150);
        assert_eq!((a - b).to_i64(), 50);
        assert_eq!((a * b).to_i64(), 5000);
        assert_eq!((a / b).to_i64(), 2);
        assert_eq!((a % b).to_i64(), 0);
    }

    #[test]
    fn test_bitwise_operations() {
        let a = i48::from_i64(0b101010);
        let b = i48::from_i64(0b110011);

        assert_eq!((a & b).to_i64(), 0b100010);
        assert_eq!((a | b).to_i64(), 0b111011);
        assert_eq!((a ^ b).to_i64(), 0b011001);
        assert_eq!((a << 2).to_i64(), 0b10101000);
        assert_eq!((a >> 2).to_i64(), 0b1010);
    }

    #[test]
    fn test_unary_operations() {
        let a = i48::from_i64(100);

        assert_eq!((-a).to_i64(), -100);
        assert_eq!((!a).to_i64(), -101);
    }

    #[test]
    fn test_from_i64() {
        assert_eq!(i48::from_i64(0).to_i64(), 0);
        assert_eq!(i48::from_i64(140737488355327).to_i64(), 140737488355327); // Max positive value
        assert_eq!(i48::from_i64(-140737488355328).to_i64(), -140737488355328); // Min negative value
    }

    #[test]
    fn test_from_bytes() {
        assert_eq!(
            i48::from_ne_bytes([0x01, 0x02, 0x03, 0x04, 0x05, 0x06]).to_i64(),
            if cfg!(target_endian = "big") {
                0x010203040506
            } else {
                0x060504030201
            }
        );
        assert_eq!(
            i48::from_le_bytes([0x01, 0x02, 0x03, 0x04, 0x05, 0x06]).to_i64(),
            0x060504030201
        );
        assert_eq!(
            i48::from_be_bytes([0x01, 0x02, 0x03, 0x04, 0x05, 0x06]).to_i64(),
            0x010203040506
        );
    }

    #[test]
    fn test_to_i64() {
        let a = i48::from_ne_bytes([0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F]);
        assert_eq!(a.to_i64(), 140737488355327); // Max positive value

        let b = i48::from_ne_bytes([0x00, 0x00, 0x00, 0x00, 0x00, 0x80]);
        assert_eq!(b.to_i64(), -140737488355328); // Min negative value
    }

    #[test]
    fn test_zero_and_one() {
        assert_eq!(i48::zero().to_i64(), 0);
        assert_eq!(i48::one().to_i64(), 1);
    }

    #[test]
    fn test_from_str() {
        assert_eq!(i48::from_str("100").unwrap().to_i64(), 100);
        assert_eq!(i48::from_str("-100").unwrap().to_i64(), -100);
        assert_eq!(
            i48::from_str("140737488355327").unwrap().to_i64(),
            140737488355327
        ); // Max positive value
        assert_eq!(
            i48::from_str("-140737488355328").unwrap().to_i64(),
            -140737488355328
        ); // Min negative value
        assert_eq!(
            i48::from_str("140737488355328").unwrap_err(),
            I48Error::OutOfRange
        );
        assert_eq!(
            i48::from_str("-140737488355329").unwrap_err(),
            I48Error::OutOfRange
        );
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", i48::from_i64(100)), "100");
        assert_eq!(format!("{}", i48::from_i64(-100)), "-100");
    }

    #[test]
    fn test_wrapping_behavior() {
        let max = i48::from_i64(140737488355327);
        assert_eq!((max + i48::one()).to_i64(), -140737488355328);

        let min = i48::from_i64(-140737488355328);
        assert_eq!((min - i48::one()).to_i64(), 140737488355327);
    }

    #[test]
    fn test_shift_operations() {
        let a = i48::from_i64(0b1);

        // Left shift
        assert_eq!((a << 47).to_i64(), -140737488355328); // 0x800000000000, which is the minimum negative value
        assert_eq!((a << 48).to_i64(), 0); // Shifts out all bits

        // Right shift
        let b = i48::from_i64(-1); // All bits set
        assert_eq!((b >> 1).to_i64(), -1); // Sign extension
        assert_eq!((b >> 47).to_i64(), -1); // Still all bits set due to sign extension
        assert_eq!((b >> 48).to_i64(), -1); // No change after 23 bits

        // Edge case: maximum positive value
        let c = i48::from_i64(0x7FFFFFFFFFFF); // 140737488355327
        assert_eq!((c << 1).to_i64(), -2); // 0xFFFFFFFFFFFE in 48-bit, which is -2 when sign-extended

        // Edge case: minimum negative value
        let d = i48::from_i64(-0x800000000000); // -140737488355328
        assert_eq!((d >> 1).to_i64(), -70368744177664); // FFFFC00000000000

        // Additional test for left shift wrapping
        assert_eq!((c << 1).to_i64(), -2); // 0xFFFFFFFFFFFE
        assert_eq!((c << 2).to_i64(), -4); // 0xFFFFFFFFFFFC
        assert_eq!((c << 3).to_i64(), -8); // 0xFFFFFFFFFFF8
    }
}
