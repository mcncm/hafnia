#![allow(unused_variables)]

use crate::{
    ast::{BinOpKind, UnOpKind},
    circuit::{BaseGateC, BaseGateQ, Cbit, FreeState, GateC, Qbit},
    mir::Operand,
    place_tree::PlaceNode,
    types::RefKind,
    values::Value,
};

use super::{
    gates,
    mem::{AsBits, BitSlice},
    *,
};

impl<'m> Interpreter<'m> {
    pub fn uncompute(&mut self, pt: GraphPt) {
        if let Some(locals) = self.st.uncompute_pts.get(&pt) {
            for local in locals {
                self.destroy(&(*local).into());
            }
        }
    }

    pub fn compute_assn(&mut self, place: &Place, rvalue: &Rvalue) {
        let bindings = match &rvalue.data {
            RvalueKind::BinOp(op, lhs, rhs) => self.compute_binop(place, op, lhs, rhs),
            RvalueKind::UnOp(op, rhs) => self.compute_unop(place, op, rhs),
            RvalueKind::Ref(kind, rplace) => self.compute_ref(kind, place, rplace),
            RvalueKind::Use(op) => self.compute_use(place, op),
            RvalueKind::Array(items) => self.compute_array(place, items),
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
        let lhs = lplace.as_bits(&self.st);
        match op {
            Operand::Const(value) => {
                let mut circ = self.circ.borrow_mut();
                circ.cnot_const(&lhs, value);
            }
            Operand::Copy(rplace) => {
                let mut dest = Destructor::from_parent(rplace, &self.st);
                let mut circ = self.circ.with_sinks(Some(&mut dest.gates), None);
                let rhs = rplace.as_bits(&self.st);
                circ.copy_into(&lhs, &rhs);
                self.st
                    .destructors
                    .insert(lplace, vec![Rc::new(RefCell::new(dest))]);
            }
            // ASSUMPTION: we're always going to copy shared references, and
            // their destructors will never mutate.
            //
            // FIXME: all kinds of assumptions won't hold after optimizations,
            // and this is not real documentation.
            Operand::Move(rplace) => {
                let mut circ = self.circ.borrow_mut();
                let rhs = rplace.as_bits(&self.st);
                circ.move_into(&lhs, &rhs);
            }
        }
    }

    pub fn compute_array(&mut self, lplace: &Place, elems: &[Operand]) {
        todo!();
    }

    pub fn compute_ref(&mut self, kind: &RefKind, lplace: &Place, rplace: &Place) {
        // Ok, double-check this, but I'm *PRETTY* sure what we want is to push
        // back any destructors from both the left *AND* right. We'll notice if
        // things aren't uncomputing correctly.
        let mut dest = Destructor::from_parents(&[lplace, rplace], &self.st);
        let rhs = rplace.as_bits(&self.st);
        let lhs = lplace.as_bits(&self.st);

        let mut circ = self.circ.with_sinks(Some(&mut dest.gates), None);
        match kind {
            RefKind::Shrd => circ.copy_into(&rhs, &lhs),
            RefKind::Uniq => {
                circ.move_into(&rhs, &lhs);
            }
        };
        self.st
            .destructors
            .insert(lplace, vec![Rc::new(RefCell::new(dest))]);
    }

    pub fn compute_drop(&mut self, place: &Place) {
        // Execute any destructors
        self.destroy(place);

        // FIXME this is just to make the hack work
        // If this is shared memory, don't write `Free` instructions
        if self.st.shared_mem_borrows.contains_key(&place.root) {
            return;
        }

        // Correctness: the destructor is done using the circuit assembler, so
        // we can borrow it here.
        let mut circ = self.circ.borrow_mut();

        let lhs = place.as_bits(&self.st);

        // Then free the bits
        let ty = self.st.type_of(place);
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
        if let Some(RefKind::Uniq) = self.st.type_of(place).ref_kind(self.ctx) {
            Some(Destructor::from_parents(parents, &self.st))
        } else {
            None
        }
    }

    fn compute_copy_copy_binop(
        &mut self,
        place: &Place,
        op: &BinOpKind,
        fst_place: &Place,
        snd_place: &Place,
    ) {
        use BinOpKind::*;
        let mut destructor = Destructor::from_parents(&[place, fst_place, snd_place], &self.st);
        let sink = &mut destructor.gates;
        let mut circ = self.circ.with_sinks(Some(sink), None);

        let lhs = &place.as_bits(&self.st);
        let fst = &fst_place.as_bits(&self.st);
        let snd = &snd_place.as_bits(&self.st);

        match op {
            Equal => {
                let xnors = circ
                    .allocators
                    .alloc_for_ty(self.st.type_of(fst_place), self.ctx);
                circ.map_cnot(fst, &xnors.as_slice());
                circ.map_cnot(snd, &xnors.as_slice());
                circ.map_not(&xnors.as_slice());
                // Should have a generalized AND.
                let mut and_gate: GateQ = BaseGateQ::X(lhs.qbits[0]).into();
                and_gate.ctrls = xnors.qbits.iter().map(|q| (*q, true)).collect();
                circ.push_qgate(and_gate);
                // FIXME classical case
                destructor.ancillas = xnors.qbits;
            }
            Nequal => {
                if self.st.type_of(fst_place) != self.ctx.common.shrd_q_bool {
                    // for larger types, we have to take the AND of the XNORs,
                    // which means allocating intermediates. This isn't
                    // something we're going to be able to tackle in five
                    // minutes.
                    unimplemented!();
                }
                // For `&?bool`s, though, NEQUAL == XOR.
                circ.map_cnot(fst, lhs);
                circ.map_cnot(snd, lhs);
            }
            DotDot => {}
            Plus => {
                // FIXME quantum case only for now
                assert_eq!(fst.cbits.len(), 0);
                let snd = snd.qbits;
                circ.map_cnot(fst, lhs);
                circ.draper_addition(lhs.qbits, snd);
            }
            Minus => {}
            Times => {}
            Mod => {}
            Less => {}
            Greater => {}
            Swap => {
                circ.map_swap(fst, snd);
            }

            And => {
                circ.map_ccnot(lhs, fst, true, snd, true);
            }

            Or => {
                circ.map_ccnot(lhs, fst, false, snd, false);
                circ.map_not(lhs);
            }

            Xor => {
                // NOTE: the control and target arguments here are in the
                // *correct* order, they're just confusing. You can refactor later.
                circ.map_cnot(fst, lhs);
                circ.map_cnot(snd, lhs);
            }
        }

        // We're still holding this borrow. Relinquish it before possibly
        // executing a destructor.
        drop(circ);
        // create the node if there is none yet
        let dest = self
            .st
            .destructors
            .create_node(place)
            .this
            .get_or_insert_with(Vec::new);
        dest.clear();
        dest.push(Rc::new(RefCell::new(destructor)));
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
        let lhs = &lplace.as_bits(&self.st);
        let (rhs, mut destructor) = match right {
            /*
             * Could consider breaking this out into a separate function
             */
            Operand::Const(value) => {
                return match op {
                    UnOpKind::Minus => todo!(),
                    UnOpKind::Linear => {
                        let mut circ = self.circ.borrow_mut();
                        circ.map_init(lhs);
                        circ.cnot_const(lhs, value);
                    }
                    UnOpKind::Not => todo!(),
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
                // DESTRUCTORS: Ok, but do we want the parent on the lhs, too?
                // Because, we might be overwriting something in there. I think
                // we might. Let's see.
                let mut dest = Destructor::from_parents(&[lplace, rplace], &self.st);
                let rhs = rplace.as_bits(&self.st);
                let mut circ = self.circ.with_sinks(Some(&mut dest.gates), None);

                // Control first if necessary. Note that this will control
                // classical bits on classical bits and qubits on qubits.
                if lhs != &rhs {
                    debug_assert!(!lhs.qbits.iter().zip(rhs.qbits.iter()).any(|(l, r)| l == r));
                    debug_assert!(!lhs.cbits.iter().zip(rhs.cbits.iter()).any(|(l, r)| l == r));

                    // This is actually the right order
                    circ.map_cnot(&rhs, lhs);
                }

                (rhs, Some(dest))
            }

            /*
             * First, do no optimization. Moves can be eliminated later. So, by
             * default, a move will SWAP.
             */
            Operand::Move(rplace) => {
                let rhs = rplace.as_bits(&self.st);
                let mut circ = self.circ.with_sinks(None, None);
                // Swap first if necessary. Note that this will swap clasical
                // bits with classical bits and qubits with qubits.

                if lhs != &rhs {
                    // Now... We're assuming here that *all* of the bits are
                    // distinct. We should either (a) assert this fact, or (b)
                    // swap exactly the bits that differ.
                    debug_assert!(!lhs.qbits.iter().zip(rhs.qbits.iter()).any(|(l, r)| l == r));
                    debug_assert!(!lhs.cbits.iter().zip(rhs.cbits.iter()).any(|(l, r)| l == r));
                    circ.mapgate_pair(
                        lhs,
                        &rhs,
                        Some(|(_, u, v)| BaseGateQ::Swap(u, v)),
                        Some(|(_, u, v)| BaseGateC::Swap(u, v)),
                    );
                }

                (rhs, None)
            }
        };

        // Take a handle to the gate sink, if there is one.
        let sink = destructor.as_mut().map(|dest| &mut dest.gates);
        let mut circ = self.circ.with_sinks(sink, None);

        /*
         Now we should be able to operate in-place on the left-hand side.

         In fact, this *won't* be in-place, because we're not yet computing
         adresses in advance of gates. But we'll at least only have to edit this
         from here on to fix that.
        */

        match op {
            UnOpKind::Minus => todo!(),

            UnOpKind::Not => {
                circ.map_not(lhs);
            }

            UnOpKind::Split => {
                circ.map_hadamard(lhs);
            }

            UnOpKind::Linear => {
                // In particular, this should *not* receive a control, even if
                // it appears under a control, because the created qubits could
                // outlive any reference.
                //
                // ...Right? I *THINK* that's right. Ach, we *really* have to be sure about this case, though.
                let not = |(_, ctrl, tgt)| BaseGateQ::X(tgt);
                // This is the correct argument order. That could be confusing.
                circ.mapgate_class_ctrl(&rhs, lhs, Some(not));
            }
            UnOpKind::Delin => {
                circ.meas(rhs.qbits, lhs.cbits, &self.st);
            }
        };

        /*
        Finally, insert the destructor, if there is one, and make it immutable
        for all time.
        */
        if let Some(destructor) = destructor {
            self.st
                .destructors
                .insert(lplace, vec![Rc::new(RefCell::new(destructor))]);
        }
    }
}
