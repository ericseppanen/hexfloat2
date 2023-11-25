use std::ops::{Deref, DerefMut};

mod float;
mod format;
mod parse;

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
