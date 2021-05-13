#![allow(unused_variables)]

use crate::{
    ast::{BinOpKind, UnOpKind},
    circuit::{BaseGateC, BaseGateQ, Cbit, FreeState, GateC, Qbit},
    mir::Operand,
    types::RefKind,
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
    // NOTE: this function is probably just wrong. We probably don't want to
    // delegate all the `memcpy`ing to these `Rvalue`-specific methods.
    //
    // The deputy methods should *probably* just get a pile of bits.
    pub fn compute_assn(&mut self, place: &Place, rvalue: &Rvalue) {
        let bindings = match &rvalue.data {
            RvalueKind::BinOp(op, lhs, rhs) => self.compute_binop(place, op, lhs, rhs),
            RvalueKind::UnOp(op, rhs) => self.compute_unop(place, op, rhs),
            RvalueKind::Ref(_, rplace) => self.st.env.memcpy(place, rplace),
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

    fn compute_use(&mut self, lplace: &Place, op: &Operand) {
        match op {
            Operand::Const(value) => {}
            Operand::Copy(rplace) => {
                // NOTE not actually correct
                self.st.env.memcpy(lplace, rplace);
            }
            // NOTE: When is this correct/safe? When should we swap? Can we
            // always mem_copy?
            Operand::Move(rplace) => {
                self.st.env.memcpy(lplace, rplace);
            }
        }
    }

    pub fn compute_drop(&mut self, place: &Place) {
        // Execute any destructors
        self.st.env.bindings[place.root].destructor.take();

        // Correctness: the destructor is done using the circuit assembler, so
        // we can borrow it here.
        let mut circ = self.circ.borrow_mut();

        let lhs = place.as_bits(&self.st.env);

        // Then free the bits
        let ty = self.st.env.type_of(place);
        if let Some(RefKind::Shrd) = ty.ref_kind(self.ctx) {
            circ.map_free(&lhs, |(_, _)| FreeState::Clean, |(_, _)| FreeState::Clean);
        } else {
            // This is *WAY* too conservative: reference fields of an owned tuple
            // will be dropped dirtily.
            circ.map_free(&lhs, |(_, _)| FreeState::Dirty, |(_, _)| FreeState::Dirty);
        }
    }

    fn compute_binop(&mut self, place: &Place, op: &BinOpKind, left: &Operand, right: &Operand) {
        use Operand::*;

        match (left, right) {
            (Copy(arg), Const(value)) | (Const(value), Copy(arg)) => {
                return self.compute_place_const_binop(place, op, arg, value)
            }

            (Const(left), Const(right)) => {
                // Basically a single step of constant propagation
                return self.compute_const_const_binop(place, op, left, right);
            }
            /*
            For now, assume that any move is impossible. (This is blatantly
            wrong: could be `&mut` refs in a `$`, could be a post-optimization
            `&` ref...).
            */
            (Operand::Move(_), _) | (_, Operand::Move(_)) => todo!(),

            (Copy(left), Copy(right)) => self.compute_copy_copy_binop(place, op, left, right),
        }
    }

    // TODO: Figure out where to put this and how it affects the factoring of
    // this module.
    fn destructor_for(&mut self, place: &Place, parents: &[&Place]) -> Option<Destructor<'m>> {
        if let Some(RefKind::Uniq) = self.st.env.type_of(place).ref_kind(self.ctx) {
            Some(Destructor::from_parents(parents, self))
        } else {
            None
        }
    }

    fn compute_copy_copy_binop(&mut self, place: &Place, op: &BinOpKind, fst: &Place, snd: &Place) {
        use BinOpKind::*;
        // Correctness: this is safe because we can't destroy a reference during
        // a binop.
        let mut circ = self.circ.borrow_mut();

        let mut destructor = Destructor::from_parents(&[fst, snd], self);
        let sink = &mut destructor.gates;

        let lhs = &place.as_bits(&self.st.env);
        let fst = &fst.as_bits(&self.st.env);
        let snd = &snd.as_bits(&self.st.env);

        match op {
            Equal => {}
            Nequal => {}
            DotDot => {}
            Plus => {}
            Minus => {}
            Times => {}
            Mod => {}
            Less => {}
            Greater => {}
            Swap => {}
            And => {
                let quant = |(idx, fst, snd)| {
                    let lhs = lhs.qbits[idx];
                    GateQ {
                        ctrls: vec![fst, snd],
                        base: BaseGateQ::X(lhs),
                    }
                };
                let quant = util::tee(quant, sink);

                let class = |(idx, fst, snd)| {
                    let lhs = lhs.cbits[idx];
                    GateC {
                        ctrls: vec![fst, snd],
                        base: BaseGateC::Not(lhs).into(),
                    }
                };
                circ.mapgate_pair(fst, snd, Some(quant), Some(class));
            }
            Or => {}
            Xor => {}
        }

        self.st.env.bindings[place.root]
            .destructor
            .replace(Rc::new(destructor));
    }

    fn compute_place_const_binop(
        &mut self,
        place: &Place,
        op: &BinOpKind,
        arg: &Place,
        value: &Value,
    ) {
        todo!()
    }

    fn compute_const_const_binop(
        &mut self,
        place: &Place,
        op: &BinOpKind,
        left: &Value,
        right: &Value,
    ) {
        todo!()
    }

    fn compute_unop(&mut self, lplace: &Place, op: &UnOpKind, right: &Operand) {
        // Correctness: this is safe because we can't drop any ancillas here
        let mut circ = self.circ.borrow_mut();

        let lhs = lplace.as_bits(&self.st.env);
        let (rhs, mut destructor) = match right {
            /*
             * Could consider breakign this out into a separate function
             */
            Operand::Const(value) => {
                return match op {
                    UnOpKind::Minus => todo!(),
                    UnOpKind::Not => {
                        circ.cnot_const(&lhs, value);
                    }
                    _ => {}
                }
            }

            /*
             * Classical data is an "edge case" here, because the lhs isn't
             * guaranteed to be uninitialized. But if this is quantum data, the
             * lhs *must* be a fresh qubit, and we can just control on the rhs.
             *
             * Do we want to identify '`Copy` + quantum' with 'shared reference'?
             * Are there cases where `Move` makes more sense, for example after
             * certain optimizations?
             */
            Operand::Copy(rplace) => {
                let parent = self.st.env.bindings[rplace.root]
                    .destructor
                    .as_ref()
                    .map(|dest| dest.clone());
                // Is always safe to put a new one in here?
                let dest = Destructor::new(&self.circ);
                let bits = rplace.as_bits(&self.st.env);
                (bits, Some(dest))
            }

            /*
             * First, do no optimization. Moves can be eliminated later. So, by
             * default, a move will SWAP.
             */
            Operand::Move(rplace) => {
                let bits = rplace.as_bits(&self.st.env);
                (bits, None)
            }
        };

        // Take a handle to the gate sink, if there is one.
        let sink = destructor.as_mut().map(|dest| &mut dest.gates);

        /*
         Now we should be able to operate in-place on the left-hand side.

         In fact, this *won't* be in-place, because we're not yet computing
         adresses in advance of gates. But we'll at least only have to edit this
         from here on to fix that.
        */

        match op {
            UnOpKind::Minus => todo!(),

            UnOpKind::Not => {
                // FIXME: not correct any more: need to swap first.

                // NOTE: this check defeats the purpose of the abstraction--but
                // it's convenient for validation!
                if sink.is_some() {
                    circ.mapgate_sq(&lhs, |u| BaseGateQ::X(u), sink);
                } else {
                    circ.map_not(&lhs);
                }
            }

            UnOpKind::Split => {
                circ.map_hadamard(&lhs);
            }

            UnOpKind::Linear => {
                let not = |(_, ctrl, tgt)| BaseGateQ::X(tgt);
                // FIXME which side where?
                circ.mapgate_class_ctrl(&lhs, &rhs, Some(not));
            }
            UnOpKind::Delin => {
                circ.meas(&rhs.qbits, &lhs.cbits, &self.st);
            }
        };

        /*
        Finally, insert the destructor, if there is one, and make it immutable
        for all time.
        */
        if let Some(destructor) = destructor {
            self.st.env.bindings[lplace.root]
                .destructor
                .replace(Rc::new(destructor));
        }
    }
}
