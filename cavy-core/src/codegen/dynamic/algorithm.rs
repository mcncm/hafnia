//! Implementations of basic quantum algorithm components

use crate::circuit::{BaseGateQ, GateQ, Qbit};

use super::CircAssembler;

impl<'a, 'c> CircAssembler<'a, 'c> {
    /// The unoptimized "basic" quantum fourier transform
    pub fn qft(&mut self, bits: &[Qbit]) {
        for (i, tgt) in bits.iter().enumerate() {
            self.push_qgate(BaseGateQ::H(*tgt));
            for (j, src) in bits[(i + 1)..].iter().enumerate() {
                let phase = 2.0 / (2 << j) as f32;
                self.push_qgate(BaseGateQ::Phase(*tgt, phase).control(*src));
            }
        }
    }

    /// The O(n^2) depth form of [Draper's addition
    /// algorithm](https://arxiv.org/abs/quant-ph/0008033). This implementation
    /// adds `inc` in-place into `acc`.
    pub fn draper_addition(&mut self, acc: &[Qbit], inc: &[Qbit]) {
        for (i, acc) in acc.iter().enumerate() {
            for (j, inc) in inc[i..].iter().enumerate() {
                let phase = 2.0 / (2 << j) as f32;
                self.push_qgate(BaseGateQ::Phase(*acc, phase).control(*inc));
            }
        }
    }
}
