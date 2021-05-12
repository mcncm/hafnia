#![allow(unused_variables)]

use crate::{
    ast::{BinOpKind, UnOpKind},
    circuit::{BaseGateC, BaseGateQ, Cbit, GateC, Qbit},
    mir::Operand,
    values::Value,
};

use super::{
    gates,
    mem::{AsBits, BitSlice},
    *,
};

enum Data {
    Place(Place),
    Const(()),
}

impl<'m> Interpreter<'m> {
    pub fn compute_assn(&mut self, place: &Place, rvalue: &Rvalue) {
        let bindings = match &rvalue.data {
            RvalueKind::BinOp(op, lhs, rhs) => self.compute_binop(place, op, lhs, rhs),
            RvalueKind::UnOp(op, rhs) => self.compute_unop(place, op, rhs),
            RvalueKind::Ref(_, rplace) => self.st.env.mem_copy(place, rplace),
            RvalueKind::Use(op) => self.compute_use(place, op),
        };
    }

    fn unwrap_operand<'a>(&mut self, op: &'a Operand) -> &'a Place {
        match op {
            Operand::Const(c) => todo!(),
            Operand::Copy(place) => place,
            Operand::Move(place) => place,
        }
    }

    fn initialize(&mut self, place: &Place, value: &Value) -> BitArray {
        let bits = value.bits();
        let allocation = self.alloc_for_place(place);
        self.map_not(&allocation);
        allocation
    }

    fn compute_use(&mut self, lplace: &Place, op: &Operand) {
        match op {
            Operand::Const(value) => {}
            Operand::Copy(rplace) => {
                // NOTE not actually correct
                self.st.env.mem_copy(lplace, rplace);
            }
            // NOTE: When is this correct/safe? When should we swap? Can we
            // always memcpy?
            Operand::Move(rplace) => {
                self.st.env.mem_copy(lplace, rplace);
            }
        }
    }

    fn compute_binop(&mut self, place: &Place, op: &BinOpKind, left: &Operand, right: &Operand) {
        let lplace = self.unwrap_operand(left);
        let rplace = self.unwrap_operand(right);
        use BinOpKind::*;
        match op {
            Equal => todo!(),
            Nequal => todo!(),
            DotDot => todo!(),
            Plus => todo!(),
            Minus => todo!(),
            Times => todo!(),
            Mod => todo!(),
            Less => todo!(),
            Greater => todo!(),
            Swap => {
                let lbits = self.st.env.bits_at(lplace);
                let rbits = self.st.env.bits_at(rplace);
                for (laddr, raddr) in lbits.qbits.iter().zip(rbits.qbits.iter()) {
                    self.circ
                        .push_qgate(BaseGateQ::Swap(*laddr, *raddr), &self.st);
                }
            }
            And => todo!(),
            Or => todo!(),
            Xor => todo!(),
        }
    }

    fn compute_unop(&mut self, lplace: &Place, op: &UnOpKind, right: &Operand) {
        match right {
            Operand::Const(_) => {}

            /*
            Classical data is an "edge case" here, because the lhs isn't
            guaranteed to be uninitialied. But if this is quantum data, the
            lhs *must* be a fresh qubit, and we can just control on the rhs.
            */
            Operand::Copy(_) => {}

            /*
            First, do no optimization. Moves can be eliminated later. So, by
            default, a move will SWAP.
            */
            Operand::Move(_) => {}
        };

        /*
         Now we can operate in-place on the left-hand side.
        */

        let bitset = match op {
            UnOpKind::Minus => todo!(),
            UnOpKind::Not => {
                let rplace = self.unwrap_operand(right);
                let bits = self.st.env.bits_at(rplace).to_owned();
                self.map_not(&bits.as_ref());
                bits.to_owned()
            }
            UnOpKind::Split => {
                let rplace = self.unwrap_operand(right);
                let bits = self.st.env.bits_at(rplace);
                for addr in bits.qbits {
                    self.circ.push_qgate(BaseGateQ::H(*addr), &self.st);
                }
                bits.to_owned()
            }
            UnOpKind::Linear => match right {
                Operand::Const(value) => {
                    let allocation = self.initialize(lplace, value);
                    allocation
                }
                Operand::Copy(_) => {
                    unimplemented!("Classical feedback not yet implemented")
                }
                Operand::Move(_) => {
                    unimplemented!("Classical feedback not yet implemented")
                }
            },
            UnOpKind::Delin => {
                let rplace = self.unwrap_operand(right);
                let allocation = self.alloc_for_place(lplace);
                let qbits = self.st.env.bits_at(rplace).qbits;
                self.circ.meas(qbits, &allocation.cbits, &self.st);
                allocation
            }
        };
        self.st.env.insert(lplace, bitset.as_ref());
    }

    /// Swap all the bits--classical and quantum--in two places, which should be
    /// of the same size.
    fn map_phase<B>(&mut self, obj: &B)
    where
        B: AsBits,
    {
        let phase = |_, u| [BaseGateQ::Z(u)];
        // An interesting bit of Rust type noise.
        self.mapgate_single::<_, _, _, 1, 0>(obj, Some(phase), None::<fn(_, _) -> _>);
    }

    /// NOT all the bits--classical and quantum--in one place
    fn map_not<B>(&mut self, obj: &B)
    where
        B: AsBits,
    {
        let notq = |_, u| [BaseGateQ::X(u)];
        let notc = |_, u| [BaseGateC::Not(u)];
        self.mapgate_single(obj, Some(notq), Some(notc));
    }

    /// CNOT all the bits--classical and quantum--in two places, which should be
    /// of the same size.
    fn map_cnot<B>(&mut self, ctrl: &B, tgt: &B)
    where
        B: AsBits,
    {
        let swapq = |_, ctrl, _, tgt| [BaseGateQ::Cnot { ctrl, tgt }];
        let swapc = |_, ctrl, _, tgt| [BaseGateC::Cnot { ctrl, tgt }];
        self.mapgate_two(ctrl, tgt, Some(swapq), Some(swapc));
    }

    /// SWAP all the bits--classical and quantum--in two places, which should be
    /// of the same size.
    fn map_swap<B>(&mut self, fst: &B, snd: &B)
    where
        B: AsBits,
    {
        let swapq = |_, q1, _, q2| [BaseGateQ::Swap(q1, q2)];
        // I don't have a built-in classical swap, so let's just make our own.
        let swapc = |_, c1, _, c2| {
            [
                BaseGateC::Cnot { ctrl: c1, tgt: c2 },
                BaseGateC::Cnot { ctrl: c2, tgt: c1 },
                BaseGateC::Cnot { ctrl: c1, tgt: c2 },
            ]
        };
        self.mapgate_two(fst, snd, Some(swapq), Some(swapc));
    }

    /// Map single-bit classical and quantum gates over an allocation
    fn mapgate_single<'a, B, Q, C, const N: usize, const M: usize>(
        &'a mut self,
        obj: &B,
        quant: Option<Q>,
        class: Option<C>,
    ) where
        B: AsBits,
        Q: Fn(usize, Qbit) -> [BaseGateQ; N],
        C: Fn(usize, Cbit) -> [BaseGateC; M],
    {
        let bits = obj.as_bits(&self.st.env);

        if let Some(f) = quant {
            for (idx, qbit) in bits.qbits.iter().enumerate() {
                // NOTE: these copies shouldn't be necessary--this will be fixed
                // when arrays become iterable in Rust 2021.
                for gate in f(idx, *qbit).iter() {
                    self.circ.push_qgate(*gate, &self.st);
                }
            }
        }

        if let Some(g) = class {
            for (idx, cbit) in bits.cbits.iter().enumerate() {
                for gate in g(idx, *cbit).iter() {
                    self.circ.push_cgate(*gate, &self.st);
                }
            }
        }
    }

    /// Map two-bit classical and quantum gates over an allocation
    fn mapgate_two<'a, B, Q, C, const N: usize, const M: usize>(
        &'a mut self,
        fst: &B,
        snd: &B,
        quant: Option<Q>,
        class: Option<C>,
    ) where
        B: AsBits,
        Q: Fn(usize, Qbit, usize, Qbit) -> [BaseGateQ; N],
        C: Fn(usize, Cbit, usize, Cbit) -> [BaseGateC; M],
    {
        let fst_bits = fst.as_bits(&self.st.env);
        let snd_bits = snd.as_bits(&self.st.env);

        if let Some(f) = quant {
            for ((fst_idx, fst_qbit), (snd_idx, snd_qbit)) in fst_bits
                .qbits
                .iter()
                .enumerate()
                .zip(snd_bits.qbits.iter().enumerate())
            {
                for gate in f(fst_idx, *fst_qbit, snd_idx, *snd_qbit).iter() {
                    self.circ.push_qgate(*gate, &self.st);
                }
            }
        }

        if let Some(f) = class {
            for ((fst_idx, fst_cbit), (snd_idx, snd_cbit)) in fst_bits
                .cbits
                .iter()
                .enumerate()
                .zip(snd_bits.cbits.iter().enumerate())
            {
                for gate in f(fst_idx, *fst_cbit, snd_idx, *snd_cbit).iter() {
                    self.circ.push_cgate(*gate, &self.st);
                }
            }
        }
    }
}
