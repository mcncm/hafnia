use super::*;

use crate::circuit::Inst;
use std::fmt;

#[derive(Debug)]
pub struct SerialDebug;

impl FmtWith<SerialDebug> for CircuitBuf {
    fn fmt(&self, _: &SerialDebug, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for inst in self.iter() {
            writeln!(f, "{:?}", inst)?;
        }
        Ok(())
    }
}
