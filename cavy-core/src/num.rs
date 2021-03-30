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
