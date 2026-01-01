use core::fmt::{Display, Write};
use core::num::FpCategory;

use crate::float::FloatBits;
use crate::HexFloat;

// FIXME: we should also impl the UpperHex and LowerHex traits.

impl<F> Display for HexFloat<F>
where
    F: FloatBits + Display,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let (sign, exponent, mantissa) = self.to_parts();

        match self.category() {
            FpCategory::Nan | FpCategory::Infinite => {
                return self.0.fmt(f);
            }
            FpCategory::Zero => {
                if sign {
                    f.write_char('-')?;
                }
                return f.write_str("0x0.0p0");
            }
            _ => {}
        };

        let bias = i32::from(F::EXPONENT_BIAS);
        // The mantissa MSB needs to be shifted up to the nearest nibble.
        let mshift = (4 - u32::from(F::MANTISSA_BITS) % 4) % 4;
        let mantissa = mantissa << mshift;
        // The width is rounded up to the nearest char (4 bits)
        let mwidth = (F::MANTISSA_BITS as usize + 3) / 4;
        let sign_char = if sign { "-" } else { "" };
        let mut exponent: i32 = exponent.into() - bias;
        let leading = if exponent == -bias {
            // subnormal number means we shift our output by 1 bit.
            exponent += 1;
            "0."
        } else {
            "1."
        };

        write!(f, "{sign_char}0x{leading}{mantissa:0mwidth$x}p{exponent}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_f32() {
        assert_eq!(HexFloat::from(0.0f32).to_string(), "0x0.0p0");
        assert_eq!(HexFloat::from(1.0f32).to_string(), "0x1.000000p0");
        assert_eq!(HexFloat::from(1.5f32).to_string(), "0x1.800000p0");
        assert_eq!(HexFloat::from(1.25f32).to_string(), "0x1.400000p0");
        assert_eq!(HexFloat::from(1.125f32).to_string(), "0x1.200000p0");
        assert_eq!(HexFloat::from(1.03125f32).to_string(), "0x1.080000p0");
        assert_eq!(HexFloat::from(1.0000001_f32).to_string(), "0x1.000002p0");
    }

    #[test]
    fn test_format_f64() {
        assert_eq!(HexFloat::from(0.0f64).to_string(), "0x0.0p0");
        assert_eq!(HexFloat::from(1.0f64).to_string(), "0x1.0000000000000p0");
        assert_eq!(
            HexFloat::from(1.0000000000000002_f64).to_string(),
            "0x1.0000000000001p0"
        );
    }
}
