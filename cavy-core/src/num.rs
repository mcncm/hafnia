//! Cavy's numeric values. This is broken out into a separate module because the
//! types defined here are used by both `annot.rs` and `types.rs`.

use crate::token::Lexeme;
use std::fmt;

/// The raw number representation. This should be equal to the largest numeric
/// size supported by the object language.
pub type NativeNum = u32;

/// The type of an unsigned integer. The variants of this type correspond to the
/// integer sizes supported by Cavy, and their concrete values are their sizes
/// in bits.
#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Uint {
    U2 = 2,
    U4 = 4,
    U8 = 8,
    U16 = 16,
    U32 = 32,
}

impl Uint {
    pub fn from_lexeme(lexeme: Lexeme) -> Result<Self, ()> {
        #![allow(clippy::result_unit_err)]
        let u = match lexeme {
            Lexeme::U4 => Self::U4,
            Lexeme::U8 => Self::U8,
            Lexeme::U16 => Self::U16,
            Lexeme::U32 => Self::U32,
            _ => return Err(()),
        };
        Ok(u)
    }
}

impl fmt::Display for Uint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let repr = match self {
            Self::U2 => "u2",
            Self::U4 => "u4",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
        };
        write!(f, "{}", repr)
    }
}

/// A struct for holding small unsigned integers; that is, smaller than a u8. In
/// principle we could back these with a u64 or something, and have one for
/// every possible size, but let's stick to u2 and u4 for now.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct USmall<const N: usize>(u8);

impl<const N: usize> USmall<N> {
    /// The wrapping modulus of the small integer; that is, 1 + its maximum element.
    const MOD: u8 = 1 << N;
    const MAX: u8 = Self::MOD - 1;

    // Arithmetic: let's not implement `std::ops::{Add, Mul}` for these, because
    // apparently those don't wrap for in release mode for primitive types like
    // I thought they did. We'll only ever call the `wrapping_` methods for those, instead.

    /// Wrapping addition on small unsigned integers
    /// NOTE: this will be correct as long as `N` is {2, 4}.
    pub fn wrapping_add(self, rhs: Self) -> Self {
        Self(self.0.wrapping_add(rhs.0) % Self::MOD)
    }

    /// Wrapping multiplication on small unsigned integers
    /// NOTE: this will be correct as long as `N` is {2, 4}.
    pub fn wrapping_mul(self, rhs: Self) -> Self {
        Self(self.0.wrapping_mul(rhs.0) % Self::MOD)
    }
}

impl<const N: usize> std::ops::Not for USmall<N> {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(!self.0 & Self::MAX)
    }
}

// === boilerplate impls ===

impl<const N: usize> From<USmall<N>> for u8 {
    fn from(n: USmall<N>) -> Self {
        n.0
    }
}

impl<const N: usize> From<u8> for USmall<N> {
    fn from(n: u8) -> Self {
        Self(n)
    }
}

impl<const N: usize> std::fmt::Debug for USmall<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl<const N: usize> std::fmt::Display for USmall<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
