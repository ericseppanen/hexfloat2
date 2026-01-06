use core::cmp::min;
use core::fmt::{Display, Write};
use core::num::FpCategory;

use crate::float::{FloatBits, MantissaOps as _};
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
        let mut mantissa = mantissa << mshift;

        let trailing_zero_bits = mantissa.trailing_zeroes();
        let trailing_zero_chars = trailing_zero_bits / 4;
        // Always print at least one mantissa digit.
        // But don't allow printing more mantissa digits than we have in the mantissa integer.
        let mantissa_max_chars = (F::MANTISSA_BITS as u32 + 3) / 4;
        let precision: u32 = f
            .precision()
            .unwrap_or(0)
            .try_into()
            .expect("precision out of range");
        let precision = precision.clamp(1, mantissa_max_chars);

        // There's no definition for how rounding should work in IEEE754,
        // so we don't provide a way to do reduced precision. We only use
        // the precision option to set the number of trailing zeroes.
        let remove_chars_from_right = min(trailing_zero_chars, mantissa_max_chars - precision);
        mantissa = mantissa >> (remove_chars_from_right * 4);

        let mwidth = (mantissa_max_chars - remove_chars_from_right) as usize;

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
        assert_eq!(HexFloat::from(1.0f32).to_string(), "0x1.0p0");
        assert_eq!(HexFloat::from(1.5f32).to_string(), "0x1.8p0");
        assert_eq!(HexFloat::from(1.25f32).to_string(), "0x1.4p0");
        assert_eq!(HexFloat::from(1.125f32).to_string(), "0x1.2p0");
        assert_eq!(HexFloat::from(1.03125f32).to_string(), "0x1.08p0");
        assert_eq!(HexFloat::from(1.0000001_f32).to_string(), "0x1.000002p0");
    }

    #[test]
    fn test_format_f64() {
        assert_eq!(HexFloat::from(0.0f64).to_string(), "0x0.0p0");
        assert_eq!(HexFloat::from(1.0f64).to_string(), "0x1.0p0");
        assert_eq!(HexFloat::from(1.5f64).to_string(), "0x1.8p0");
        assert_eq!(HexFloat::from(1.25f64).to_string(), "0x1.4p0");
        assert_eq!(HexFloat::from(1.125f64).to_string(), "0x1.2p0");
        assert_eq!(HexFloat::from(1.03125f64).to_string(), "0x1.08p0");
        assert_eq!(
            HexFloat::from(1.0000000000000002_f64).to_string(),
            "0x1.0000000000001p0"
        );
    }

    #[test]
    fn test_format_precision() {
        // f32, reducing precision has no effect.
        let value = crate::parse::<f32>("0x1.111112p0").unwrap();
        assert_eq!(format!("{:0.1}", HexFloat::from(value)), "0x1.111112p0");
        assert_eq!(format!("{:0.5}", HexFloat::from(value)), "0x1.111112p0");
        assert_eq!(format!("{:0.6}", HexFloat::from(value)), "0x1.111112p0");
        assert_eq!(format!("{:0.7}", HexFloat::from(value)), "0x1.111112p0");

        // f64, reducing precision has no effect.
        let value = crate::parse::<f64>("0x1.1111111111111p0").unwrap();
        assert_eq!(
            format!("{:0.1}", HexFloat::from(value)),
            "0x1.1111111111111p0"
        );
        assert_eq!(
            format!("{:0.5}", HexFloat::from(value)),
            "0x1.1111111111111p0"
        );
        assert_eq!(
            format!("{:0.13}", HexFloat::from(value)),
            "0x1.1111111111111p0"
        );
        assert_eq!(
            format!("{:0.14}", HexFloat::from(value)),
            "0x1.1111111111111p0"
        );

        // f32, adding extra precision characters.
        assert_eq!(format!("{:0.1}", HexFloat::from(1.0f32)), "0x1.0p0");
        assert_eq!(format!("{:0.2}", HexFloat::from(1.0f32)), "0x1.00p0");
        assert_eq!(format!("{:0.3}", HexFloat::from(1.0f32)), "0x1.000p0");
        assert_eq!(format!("{:0.5}", HexFloat::from(1.0f32)), "0x1.00000p0");
        assert_eq!(format!("{:0.6}", HexFloat::from(1.0f32)), "0x1.000000p0");
        assert_eq!(format!("{:0.7}", HexFloat::from(1.0f32)), "0x1.000000p0");

        // f64, adding extra precision characters.
        assert_eq!(format!("{:0.1}", HexFloat::from(1.0f64)), "0x1.0p0");
        assert_eq!(format!("{:0.2}", HexFloat::from(1.0f64)), "0x1.00p0");
        assert_eq!(format!("{:0.3}", HexFloat::from(1.0f64)), "0x1.000p0");
        assert_eq!(
            format!("{:0.12}", HexFloat::from(1.0f64)),
            "0x1.000000000000p0"
        );
        assert_eq!(
            format!("{:0.13}", HexFloat::from(1.0f64)),
            "0x1.0000000000000p0"
        );
        assert_eq!(
            format!("{:0.14}", HexFloat::from(1.0f64)),
            "0x1.0000000000000p0"
        );
        assert_eq!(
            format!("{:0.15}", HexFloat::from(1.0f64)),
            "0x1.0000000000000p0"
        );
    }
}
