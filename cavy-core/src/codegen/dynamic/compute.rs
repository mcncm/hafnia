#![allow(unused_variables)]

use crate::{ast::UnOpKind, mir::Operand, values::Value};

use super::{gates, mem::BitSetSlice, *};

enum Data {
    Place(Place),
    Const(()),
}

impl<'m> Interpreter<'m> {
    pub fn compute_assn(&mut self, place: &Place, rvalue: &Rvalue) {
        let bindings = match &rvalue.data {
            RvalueKind::BinOp(_, _, _) => todo!(),
            RvalueKind::UnOp(op, rhs) => self.compute_unop(place, op, rhs),
            RvalueKind::Ref(_, _) => todo!(),
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

    fn initialize(&mut self, place: &Place, value: &Value) -> BitSet {
        let bits = value.bits();
        let allocation = self.alloc_for_place(place);
        for (i, b) in value.bits().iter().enumerate() {
            if *b {
                let addr = allocation.qbits[i];
                self.circ.push(QGate::X(addr), &self.st);
            }
        }
        allocation
    }

    fn compute_use(&mut self, lplace: &Place, op: &Operand) {
        match op {
            Operand::Const(value) => {}
            Operand::Copy(rplace) => {
                // NOTE not actually correct
                self.st.env.mem_copy(lplace, rplace);
            }
            Operand::Move(rplace) => {
                self.st.env.mem_copy(lplace, rplace);
            }
        }
    }

    fn compute_unop(&mut self, place: &Place, op: &UnOpKind, right: &Operand) {
        let bitset = match op {
            UnOpKind::Minus => todo!(),
            UnOpKind::Not => {
                let rplace = self.unwrap_operand(right);
                let bits = self.st.env.bits_at(rplace);
                for addr in bits.qbits {
                    self.circ.push(QGate::X(*addr), &self.st);
                }
                bits
            }
            UnOpKind::Split => {
                let rplace = self.unwrap_operand(right);
                let bits = self.st.env.bits_at(rplace);
                for addr in bits.qbits {
                    self.circ.push(QGate::H(*addr), &self.st);
                }
                bits
            }
            UnOpKind::Linear => {
                match right {
                    Operand::Const(value) => {
                        let allocation = self.initialize(place, value);
                        self.st.env.insert(place, allocation.as_ref());
                    }
                    Operand::Copy(_) => {
                        unimplemented!("Classical feedback not yet implemented")
                    }
                    Operand::Move(_) => {
                        unimplemented!("Classical feedback not yet implemented")
                    }
                }
                // self.insert_bindings(&lplace, allocation);
                return;
            }
            UnOpKind::Delin => {
                let rplace = self.unwrap_operand(right);
                let bits = self.st.env.bits_at(rplace);
                self.circ.meas(bits.qbits, bits.cbits, &self.st);
                bits
            }
        };
    }
}
