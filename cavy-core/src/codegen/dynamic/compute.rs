#![allow(unused_variables)]

use crate::{ast::UnOpKind, mir::Operand};

use super::{gates, mem::BitSetSlice, *};

enum Data {
    Place(Place),
    Const(()),
}

impl<'m> Interpreter<'m> {
    pub fn compute(&mut self, rvalue: &Rvalue) {
        let bindings = match &rvalue.data {
            RvalueKind::BinOp(_, _, _) => todo!(),
            RvalueKind::UnOp(op, rhs) => self.compute_unop(op, rhs),
            RvalueKind::Ref(_, _) => todo!(),
            RvalueKind::Use(_) => todo!(),
        };
    }

    fn copy_of(&mut self, place: &Place) -> Place {
        todo!();
    }

    fn move_of(&mut self, place: &Place) -> Place {
        todo!();
    }

    fn unwrap_operand<'a>(&mut self, op: &'a Operand) -> &'a Place {
        match op {
            Operand::Const(c) => todo!(),
            Operand::Copy(place) => {
                self.copy_of(place);
                place
            }
            Operand::Move(place) => {
                self.move_of(place);
                place
            }
        }
    }

    fn compute_unop(&mut self, op: &UnOpKind, right: &Operand) -> BitSetSlice {
        let place = self.unwrap_operand(right);
        let bits = self.st.env.bitset_at(place);
        match op {
            UnOpKind::Minus => todo!(),
            UnOpKind::Not => {
                for addr in bits.qbits {
                    self.circ.push(Gate::X(*addr), &self.st);
                }
                bits
            }
            UnOpKind::Split => todo!(),
            UnOpKind::Linear => todo!(),
            UnOpKind::Delin => todo!(),
        }
    }
}
