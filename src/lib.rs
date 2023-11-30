//! `hexfloat2` supports hexadecimal f32/64 syntax.
//!
//! IEEE754 defines a syntax for "hexadecimal-significand character sequences"
//! that lets you write a precise representation of a floating point number.
//!
//! For example:
//! - `0x1.0p0` is just 1.0
//! - `0x8.8p1` is 8.5 * 2^1, or 17.
//! - `0x3.0p-12` is 4 * 2^-12, or 0.000732421875 in decimal.
//!
//! Unlike decimal representations, "hexfloat" representations don't
//! involve any rounding, so a format-then-parse round trip will always
//! return exactly the same original value.
//!
//! A formatted hexfloat will always appear in its "canonical" format,
//! copying the exact bit representation as closely as possible. For example,
//! the value 2^-20 will always be rendered as `0x1.0p-19`.
//!
//! The parser attempts to handle "non-canonical" representations. For example,
//! these values will all be parsed as 2^-20:
//! - `0x1.0p-20`
//! - `0x2.0p-21`
//! - `0x0.0008p-7`
//!
//! Some inputs won't parse: values with too
//! many hex digits (e.g. `0x10000000000000000p20`) will fail to parse
//! because the parser is only willing to parse up to 16 hex digits.
//! Values that are outside the range that can be represented in the
//! underlying type (f32 or f64) will also fail to parse.
//!
//! Values with excessive precision will have the trailing bits dropped.
//! For example, `0x1.0000000000000001p0` will be truncated to `1.0` when
//! parsed into a `HexFloat<f32>`.
//!
//! "Subnormal" values can be successfully formatted and parsed;
//! `0x0.000002p-127` can be parsed as an f32; anything smaller will
//! be truncated to 0.
//!
//! # Examples
//! ```
//! use hexfloat2::HexFloat32;
//!
//! const EXPECTED: f32 = 1.0 / 1048576.0;
//!
//! let x = "0x1.0p-20";
//! let fx: HexFloat32 = x.parse().unwrap();
//! assert_eq!(*fx, EXPECTED);
//!
//! let y = "0x2.0p-21";
//! let fy: HexFloat32 = y.parse().unwrap();
//! assert_eq!(*fy, EXPECTED);
//!
//! let z = "0x0.0008p-7";
//! let fz: HexFloat32 = z.parse().unwrap();
//! assert_eq!(*fz, EXPECTED);
//!
//! let sz = format!("{fz}");
//! assert_eq!(sz, "0x1.000000p-20");
//! ```
//!
//! This crate provides newtype wrappers `HexFloat<T>`, aka `HexFloat32` or
//! `HexFloat64`, that implement `Display` and `FromStr`.
//!
//! If you don't want to deal with the wrapper structs, you can also call
//! `hexfloat::parse::<T>()` or `hexfloat::format::<T>()` instead.
//!

use std::fmt::Display;
use std::ops::{Deref, DerefMut};

mod float;
mod format;
mod parse;

pub use parse::ParseError;

use crate::float::FloatBits;

/// A wrapper type for floating point values that uses "hexfloat" syntax.
///
/// When parsed or formatted, the resulting value will be in precise
/// hexadecimal format.
///
/// There are type aliases available:
/// - `HexFloat32` is equivalent to `HexFloat<f32>`
/// - `HexFloat64` is equivalent to `HexFloat<f64>`
///
/// # Examples
/// ```
/// use hexfloat2::HexFloat32;
///
/// const EXPECTED: f32 = 1.0 / 1048576.0;
///
/// let x = "0x1.0p-20";
/// let fx: HexFloat32 = x.parse().unwrap();
/// assert_eq!(*fx, EXPECTED);
///
/// let y = "0x2.0p-21";
/// let fy: HexFloat32 = y.parse().unwrap();
/// assert_eq!(*fy, EXPECTED);
///
/// let z = "0x0.0008p-7";
/// let fz: HexFloat32 = z.parse().unwrap();
/// assert_eq!(*fz, EXPECTED);
///
/// let sz = format!("{fz}");
/// assert_eq!(sz, "0x1.000000p-20");
/// ```
///
#[derive(Debug, Default, PartialEq, PartialOrd, Hash)]
pub struct HexFloat<T>(pub T);

pub type HexFloat32 = HexFloat<f32>;
pub type HexFloat64 = HexFloat<f64>;

impl<T> AsRef<T> for HexFloat<T> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T> Deref for HexFloat<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for HexFloat<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> HexFloat<T> {
    pub const fn new(value: T) -> Self {
        Self(value)
    }
}

pub trait SupportedFloat: FloatBits + Display {}
impl SupportedFloat for f32 {}
impl SupportedFloat for f64 {}

/// Parse a hexfloat string.
///
/// # Examples
/// ```
/// let value: f32 = hexfloat2::parse("0x1.8p0").unwrap();
/// assert_eq!(value, 1.5);
/// ```
pub fn parse<F>(value: &str) -> Result<F, ParseError>
where
    F: SupportedFloat,
{
    value.parse::<HexFloat<F>>().map(|hf| hf.0)
}

/// Format a floating point value using hexfloat syntax.
///
/// # Examples
/// ```
/// assert_eq!(hexfloat2::format(100.0f32), "0x1.900000p6");
/// ```
pub fn format<F: SupportedFloat>(value: F) -> String {
    HexFloat(value).to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[track_caller]
    fn round_trip_f32(val: f32) {
        let hf = HexFloat::new(val);
        let hf_string = hf.to_string();
        let hf2: HexFloat<f32> = hf_string.parse().unwrap();

        eprintln!("{val:?} -> {hf_string} -> {hf2:?} -> {hf2}");

        assert_eq!(hf2.deref(), &val);
    }

    #[test]
    fn test_round_trip_f32() {
        let mut val = 1.0f32;
        loop {
            val = val * 2.0;
            if val.is_infinite() {
                break;
            };
            round_trip_f32(val);
        }

        let mut val = 1.0f32;
        loop {
            val = val * 0.5;
            if val == 0.0 {
                break;
            };
            round_trip_f32(val);
        }
    }

    #[track_caller]
    fn round_trip_f64(val: f64) {
        let hf = HexFloat::new(val);
        let hf_string = hf.to_string();
        let hf2: HexFloat<f64> = hf_string.parse().unwrap();

        eprintln!("{val:?} -> {hf_string} -> {hf2:?} -> {hf2}");

        assert_eq!(hf2.deref(), &val);
    }

    #[test]
    fn test_round_trip_f64() {
        let mut val = 1.0f64;
        loop {
            val = val * 2.0;
            if val.is_infinite() {
                break;
            };
            round_trip_f64(val);
        }

        let mut val = 1.0f64;
        loop {
            val = val * 0.5;
            if val == 0.0 {
                break;
            };
            round_trip_f64(val);
        }
    }
}
