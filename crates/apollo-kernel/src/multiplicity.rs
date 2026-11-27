use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, AddAssign, Mul, MulAssign};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Multiplicity {
    Zero,
    One,
    Many,
}

impl Multiplicity {
    pub const ALL: [Self; 3] = [Self::Zero, Self::One, Self::Many];

    #[must_use]
    pub const fn add(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::Zero, other) | (other, Self::Zero) => other,
            (Self::One | Self::Many, Self::One | Self::Many) => Self::Many,
        }
    }

    #[must_use]
    pub const fn mul(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::Zero, _) | (_, Self::Zero) => Self::Zero,
            (Self::One, other) | (other, Self::One) => other,
            (Self::Many, Self::Many) => Self::Many,
        }
    }

    #[must_use]
    pub const fn is_erased(self) -> bool {
        matches!(self, Self::Zero)
    }

    #[must_use]
    pub const fn is_linear(self) -> bool {
        matches!(self, Self::One)
    }

    #[must_use]
    pub const fn is_unrestricted(self) -> bool {
        matches!(self, Self::Many)
    }

    #[must_use]
    pub const fn fits_in(self, available: Self) -> bool {
        match (self, available) {
            (Self::Zero, Self::Zero | Self::Many)
            | (Self::One, Self::One | Self::Many)
            | (Self::Many, Self::Many) => true,
            (Self::Zero, Self::One)
            | (Self::One, Self::Zero)
            | (Self::Many, Self::Zero | Self::One) => false,
        }
    }
}

impl Add for Multiplicity {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::add(self, rhs)
    }
}

impl AddAssign for Multiplicity {
    fn add_assign(&mut self, rhs: Self) {
        *self = Self::add(*self, rhs);
    }
}

impl Mul for Multiplicity {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::mul(self, rhs)
    }
}

impl MulAssign for Multiplicity {
    fn mul_assign(&mut self, rhs: Self) {
        *self = Self::mul(*self, rhs);
    }
}

impl PartialOrd for Multiplicity {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else if self.fits_in(*other) {
            Some(Ordering::Less)
        } else if other.fits_in(*self) {
            Some(Ordering::Greater)
        } else {
            None
        }
    }
}

impl fmt::Display for Multiplicity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Zero => f.write_str("0"),
            Self::One => f.write_str("1"),
            Self::Many => f.write_str("ω"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UsageError {
    LengthMismatch {
        expected: usize,
        actual: usize,
    },
    IndexOutOfBounds {
        index: usize,
        len: usize,
    },
    IncompatibleUsage {
        index: usize,
        used: Multiplicity,
        available: Multiplicity,
    },
}

impl fmt::Display for UsageError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LengthMismatch { expected, actual } => {
                write!(
                    f,
                    "usage length mismatch: expected {expected}, got {actual}"
                )
            }
            Self::IndexOutOfBounds { index, len } => {
                write!(f, "usage index {index} out of bounds for length {len}")
            }
            Self::IncompatibleUsage {
                index,
                used,
                available,
            } => write!(
                f,
                "variable {index} used with multiplicity {used}, but available is {available}"
            ),
        }
    }
}

impl std::error::Error for UsageError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UsageVec {
    entries: Vec<Multiplicity>,
}

impl UsageVec {
    #[must_use]
    pub fn zero(len: usize) -> Self {
        Self {
            entries: vec![Multiplicity::Zero; len],
        }
    }

    pub fn single(len: usize, index: usize, mult: Multiplicity) -> Result<Self, UsageError> {
        if index >= len {
            return Err(UsageError::IndexOutOfBounds { index, len });
        }
        let mut usage = Self::zero(len);
        usage.entries[index] = mult;
        Ok(usage)
    }

    #[must_use]
    pub fn from_slice(entries: &[Multiplicity]) -> Self {
        Self {
            entries: entries.to_vec(),
        }
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[must_use]
    pub fn as_slice(&self) -> &[Multiplicity] {
        &self.entries
    }

    #[must_use]
    pub fn scale(&self, factor: Multiplicity) -> Self {
        Self {
            entries: self.entries.iter().map(|&m| factor * m).collect(),
        }
    }

    pub fn add(&self, other: &Self) -> Result<Self, UsageError> {
        if self.entries.len() != other.entries.len() {
            return Err(UsageError::LengthMismatch {
                expected: self.entries.len(),
                actual: other.entries.len(),
            });
        }
        let entries = self
            .entries
            .iter()
            .zip(&other.entries)
            .map(|(&lhs, &rhs)| lhs + rhs)
            .collect();
        Ok(Self { entries })
    }

    pub fn check_against(&self, available: &[Multiplicity]) -> Result<(), UsageError> {
        if self.entries.len() != available.len() {
            return Err(UsageError::LengthMismatch {
                expected: available.len(),
                actual: self.entries.len(),
            });
        }
        for (index, (&used, &avail)) in self.entries.iter().zip(available).enumerate() {
            if !used.fits_in(avail) {
                return Err(UsageError::IncompatibleUsage {
                    index,
                    used,
                    available: avail,
                });
            }
        }
        Ok(())
    }

    pub fn pop_last(&mut self) -> Option<Multiplicity> {
        self.entries.pop()
    }
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use super::{Multiplicity, UsageError, UsageVec};

    #[test]
    fn satisfies_commutative_semiring_laws() {
        for a in Multiplicity::ALL {
            assert_eq!(a + Multiplicity::Zero, a);
            assert_eq!(Multiplicity::Zero + a, a);
            assert_eq!(a * Multiplicity::One, a);
            assert_eq!(Multiplicity::One * a, a);
            assert_eq!(a * Multiplicity::Zero, Multiplicity::Zero);
            assert_eq!(Multiplicity::Zero * a, Multiplicity::Zero);

            for b in Multiplicity::ALL {
                assert_eq!(a + b, b + a);
                assert_eq!(a * b, b * a);

                let mut added = a;
                added += b;
                assert_eq!(added, a + b);

                let mut multiplied = a;
                multiplied *= b;
                assert_eq!(multiplied, a * b);

                for c in Multiplicity::ALL {
                    assert_eq!((a + b) + c, a + (b + c));
                    assert_eq!((a * b) * c, a * (b * c));
                    assert_eq!(a * (b + c), (a * b) + (a * c));
                    assert_eq!((a + b) * c, (a * c) + (b * c));
                }
            }
        }
    }

    #[test]
    fn enforces_qtt_sub_usage_partial_order() {
        assert_eq!(Multiplicity::Zero.partial_cmp(&Multiplicity::One), None);
        assert_eq!(Multiplicity::One.partial_cmp(&Multiplicity::Zero), None);
        assert_eq!(
            Multiplicity::Zero.partial_cmp(&Multiplicity::Many),
            Some(Ordering::Less)
        );
        assert_eq!(
            Multiplicity::One.partial_cmp(&Multiplicity::Many),
            Some(Ordering::Less)
        );
        assert_eq!(
            Multiplicity::Many.partial_cmp(&Multiplicity::One),
            Some(Ordering::Greater)
        );
        assert_eq!(
            Multiplicity::Many.partial_cmp(&Multiplicity::Zero),
            Some(Ordering::Greater)
        );

        for a in Multiplicity::ALL {
            assert_eq!(a.partial_cmp(&a), Some(Ordering::Equal));
            for b in Multiplicity::ALL {
                if a.fits_in(b) && b.fits_in(a) {
                    assert_eq!(a, b);
                }
                for c in Multiplicity::ALL {
                    if a.fits_in(b) && b.fits_in(c) {
                        assert!(a.fits_in(c));
                    }
                    if a.fits_in(b) {
                        assert!((a + c).fits_in(b + c));
                        assert!((a * c).fits_in(b * c));
                    }
                }
            }
        }
    }

    #[test]
    fn classifies_and_formats_multiplicities() {
        assert!(Multiplicity::Zero.is_erased());
        assert!(!Multiplicity::Zero.is_linear());
        assert!(!Multiplicity::Zero.is_unrestricted());
        assert!(Multiplicity::One.is_linear());
        assert!(!Multiplicity::One.is_erased());
        assert!(Multiplicity::Many.is_unrestricted());
        assert!(!Multiplicity::Many.is_linear());

        assert_eq!(Multiplicity::Zero.to_string(), "0");
        assert_eq!(Multiplicity::One.to_string(), "1");
        assert_eq!(Multiplicity::Many.to_string(), "ω");
    }

    #[test]
    fn usage_vec_supports_single_add_scale_and_pop() {
        let empty = UsageVec::zero(0);
        assert!(empty.is_empty());
        assert_eq!(empty.len(), 0);

        let left = UsageVec::single(2, 0, Multiplicity::One);
        assert!(left.is_ok());
        let right = UsageVec::single(2, 0, Multiplicity::One);
        assert!(right.is_ok());

        let combined = left
            .as_ref()
            .ok()
            .and_then(|l| right.as_ref().ok().map(|r| l.add(r)));
        assert_eq!(
            combined,
            Some(Ok(UsageVec::from_slice(&[
                Multiplicity::Many,
                Multiplicity::Zero
            ])))
        );

        let mut scaled = UsageVec::from_slice(&[Multiplicity::One, Multiplicity::Many])
            .scale(Multiplicity::Zero);
        assert_eq!(scaled.as_slice(), &[Multiplicity::Zero, Multiplicity::Zero]);
        assert_eq!(scaled.pop_last(), Some(Multiplicity::Zero));
        assert_eq!(scaled.len(), 1);
    }

    #[test]
    fn usage_vec_checks_against_available_and_reports_errors() {
        let used = UsageVec::from_slice(&[Multiplicity::One, Multiplicity::Zero]);
        assert_eq!(
            used.check_against(&[Multiplicity::One, Multiplicity::Many]),
            Ok(())
        );

        let unused_linear = used.check_against(&[Multiplicity::One, Multiplicity::One]);
        assert_eq!(
            unused_linear,
            Err(UsageError::IncompatibleUsage {
                index: 1,
                used: Multiplicity::Zero,
                available: Multiplicity::One,
            })
        );
        if let Err(err) = unused_linear {
            assert!(err.to_string().contains("variable 1"));
        }

        let oob = UsageVec::single(2, 2, Multiplicity::One);
        assert_eq!(oob, Err(UsageError::IndexOutOfBounds { index: 2, len: 2 }));
        if let Err(err) = oob {
            assert!(err.to_string().contains("out of bounds"));
        }

        let mismatch_add = used.add(&UsageVec::zero(3));
        assert_eq!(
            mismatch_add,
            Err(UsageError::LengthMismatch {
                expected: 2,
                actual: 3,
            })
        );
        if let Err(err) = mismatch_add {
            assert!(err.to_string().contains("length mismatch"));
        }

        let mismatch_check = used.check_against(&[Multiplicity::Many]);
        assert_eq!(
            mismatch_check,
            Err(UsageError::LengthMismatch {
                expected: 1,
                actual: 2,
            })
        );
    }
}
