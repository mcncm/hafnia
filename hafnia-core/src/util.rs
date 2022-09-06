//! Global, handy traits and functions

// === formatting ===

use std::fmt;

/// A trait for formatting things with with the help of a `Context`
pub trait FmtWith<D> {
    fn fmt_with<'t>(&'t self, data: &'t D) -> FmtWrapper<'t, Self, D>
    where
        Self: Sized,
        D: Sized,
    {
        FmtWrapper { this: self, data }
    }

    fn fmt(&self, data: &D, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

/// This struct is an implementation detail of the `CtxDisplay` trait
pub struct FmtWrapper<'t, T: FmtWith<D>, D> {
    this: &'t T,
    data: &'t D,
}

impl<'t, T: FmtWith<D>, D> fmt::Display for FmtWrapper<'t, T, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        FmtWith::<D>::fmt(self.this, self.data, f)
    }
}
