use core::fmt::Display;
use core::num::FpCategory;

use crate::float::FloatBits;
use crate::HexFloat;

// FIXME: we should also impl the UpperHex and LowerHex traits.

impl<F> Display for HexFloat<F>
where
    F: FloatBits + Display,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.category() {
            FpCategory::Nan | FpCategory::Infinite => {
                return self.0.fmt(f);
            }
            _ => {}
        };
        let (sign, exponent, mantissa) = self.to_parts();

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
