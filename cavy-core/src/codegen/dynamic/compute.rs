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

    /// FIXME should maybe be an environment method in `mem.rs`?
    fn initialize(&mut self, place: &Place, value: &Value) -> BitArray {
        let bits = value.bits();
        let allocation = self.alloc_for_place(place);
        // NOTE: why is this commented line not needed?
        // self.st.env.write_bits(place, &allocation);
        self.cnot_const(&allocation, value);
        allocation
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

        // Then free the bits
        let ty = self.st.env.type_of(place);
        if let Some(RefKind::Shrd) = ty.ref_kind(self.ctx) {
            self.map_free(place, |(_, _)| FreeState::Clean, |(_, _)| FreeState::Clean);
        } else {
            // This is *WAY* too conservative: reference fields of an owned tuple
            // will be dropped dirtily.
            self.map_free(place, |(_, _)| FreeState::Dirty, |(_, _)| FreeState::Dirty);
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

    fn compute_copy_copy_binop(
        &mut self,
        place: &Place,
        op: &BinOpKind,
        left: &Place,
        right: &Place,
    ) {
        use BinOpKind::*;

        let lhs = self.alloc_for_place(place);
        let mut destructor = Destructor::from_parents(&[left, right], self);
        let sink = &mut destructor.gates;

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
                self.mapgate_pair(left, right, Some(quant), Some(class));
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
        let (bits, mut destructor) = match right {
            Operand::Const(value) => (self.initialize(lplace, value), None),

            /*
            Classical data is an "edge case" here, because the lhs isn't
            guaranteed to be uninitialized. But if this is quantum data, the
            lhs *must* be a fresh qubit, and we can just control on the rhs.

            Do we want to identify '`Copy` + quantum' with 'shared reference'?
            Are there cases where `Move` makes more sense, for example after
            certain optimizations?
            */
            Operand::Copy(rplace) => {
                let parent = self.st.env.bindings[rplace.root]
                    .destructor
                    .as_ref()
                    .map(|dest| dest.clone());
                // Is always safe to put a new one in here?
                let dest = Destructor::new(&self.circ);
                let bits = rplace.as_bits(&self.st.env).to_owned();
                (bits, Some(dest))
            }

            /*
            First, do no optimization. Moves can be eliminated later. So, by
            default, a move will SWAP.
            */
            Operand::Move(rplace) => {
                let bits = rplace.as_bits(&self.st.env).to_owned();
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
                // NOTE: this check defeats the purpose of the abstraction--but
                // it's convenient for validation!
                if sink.is_some() {
                    self.mapgate_sq(&bits, |u| BaseGateQ::X(u), sink);
                } else {
                    self.map_not(&bits);
                }

                // These addresses are being cloned a *lot*. Suggests that this
                // module isn’t factored right.
                self.st.env.memcpy(lplace, &bits);
            }
            UnOpKind::Split => {
                self.map_hadamard(&bits);
                self.st.env.memcpy(lplace, &bits);
            }
            UnOpKind::Linear => match right {
                Operand::Const(_) => {
                    // Something is suspicious about this
                    self.st.env.memcpy(lplace, &bits);
                }

                /*
                 Runtime classical control
                */
                Operand::Copy(_) | Operand::Move(_) => {
                    let allocation = self.alloc_for_place(lplace);
                    let not = |(_, ctrl, tgt)| BaseGateQ::X(tgt);
                    self.mapgate_class_ctrl(&bits, &allocation, Some(not));
                }
            },
            UnOpKind::Delin => {
                let allocation = self.alloc_for_place(lplace);
                let qbits = bits.as_bits(&self.st.env).qbits;
                self.circ
                    .borrow_mut()
                    .meas(qbits, &allocation.cbits, &self.st);
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

    fn cnot_const<B>(&mut self, obj: &B, value: &Value)
    where
        B: AsBits,
    {
        let mut circ = self.circ.borrow_mut();

        let bits = obj.as_bits(&self.st.env);
        let const_bits = value.bits();
        if bits.cbits.is_empty() {
            for (idx, u) in bits.qbits.iter().enumerate() {
                if const_bits[idx] {
                    circ.push_qgate(BaseGateQ::X(*u), &self.st);
                }
            }
        } else if bits.qbits.is_empty() {
            for (idx, u) in bits.cbits.iter().enumerate() {
                if const_bits[idx] {
                    circ.push_cgate(BaseGateC::Not(*u), &self.st);
                }
            }
        } else {
            panic!("`cnot_const` must be called on all-classical or all-quantum lhs");
        }
    }

    // == basic gate mappers ==

    /// Apply a Z gate to all the qubits
    fn map_phase<B>(&mut self, obj: &B)
    where
        B: AsBits,
    {
        let phase = |(_, u)| BaseGateQ::Z(u);
        // An interesting bit of Rust type noise.
        self.mapgate_single::<_, _, _>(obj, Some(phase), None::<fn(_) -> _>);
    }

    /// Apply an H gate to all the qubits
    fn map_hadamard<B>(&mut self, obj: &B)
    where
        B: AsBits,
    {
        let split = |(_, u)| BaseGateQ::H(u);
        // An interesting bit of Rust type noise.
        self.mapgate_single::<_, _, _>(obj, Some(split), None::<fn(_) -> _>);
    }

    /// NOT all the bits--classical and quantum--in one place
    fn map_not<B>(&mut self, obj: &B)
    where
        B: AsBits,
    {
        let notq = |(_, u)| BaseGateQ::X(u);
        let notc = |(_, u)| BaseGateC::Not(u);
        self.mapgate_single(obj, Some(notq), Some(notc));
    }

    /// CNOT all the bits--classical and quantum--in two places, which should be
    /// of the same size.
    fn map_cnot<B>(&mut self, ctrl: &B, tgt: &B)
    where
        B: AsBits,
    {
        let swapq = |(_, ctrl, tgt)| BaseGateQ::Cnot { ctrl, tgt };
        let swapc = |(_, ctrl, tgt)| BaseGateC::Cnot { ctrl, tgt };
        self.mapgate_pair(ctrl, tgt, Some(swapq), Some(swapc));
    }

    /// SWAP all the bits--classical and quantum--in two places, which should be
    /// of the same size.
    fn map_swap<B>(&mut self, fst: &B, snd: &B)
    where
        B: AsBits,
    {
        let swapq = |(_, q1, q2)| BaseGateQ::Swap(q1, q2);
        let swapc = |(_, c1, c2)| BaseGateC::Swap(c1, c2);
        self.mapgate_pair(fst, snd, Some(swapq), Some(swapc));
    }

    // == teed gate mappers

    /// The main optionally-teed mapping function for the common use case of
    /// single-qubit gates
    fn mapgate_sq<B, F>(&mut self, obj: &B, f: F, sink: Option<&mut Vec<GateQ>>)
    where
        B: AsBits,
        F: Fn(Qbit) -> BaseGateQ,
    {
        let fp = |(_, q)| f(q);

        match sink {
            Some(sink) => {
                let tee_f = util::tee(fp, sink);
                self.mapgate_single::<_, _, _>(obj, Some(tee_f), None::<fn(_) -> _>);
            }
            None => {
                self.mapgate_single::<_, _, _>(obj, Some(fp), None::<fn(_) -> _>);
            }
        }
    }

    /// The main optionally-teed mapping function for the common use case of
    /// two-qubit gates
    fn mapgate_tq<A, B, F>(&mut self, fst: &A, snd: &B, f: F, sink: Option<&mut Vec<BaseGateQ>>)
    where
        A: AsBits,
        B: AsBits,
        F: Fn(Qbit, Qbit) -> BaseGateQ,
    {
        let fp = |(_, q1, q2)| f(q1, q2);

        match sink {
            Some(sink) => {
                let tee_f = util::tee(fp, sink);
                self.mapgate_pair::<_, _, _, _, _, GateC>(
                    fst,
                    snd,
                    Some(tee_f),
                    None::<fn(_) -> GateC>,
                );
            }
            None => {
                self.mapgate_pair::<_, _, _, _, _, GateC>(
                    fst,
                    snd,
                    Some(fp),
                    None::<fn(_) -> GateC>,
                );
            }
        }
    }

    /// Map single-bit classical and quantum gates over an allocation
    fn mapgate_single<'a, B, Q, C>(&'a mut self, obj: &B, quant: Option<Q>, class: Option<C>)
    where
        B: AsBits,
        Q: FnMut((usize, Qbit)) -> BaseGateQ,
        C: FnMut((usize, Cbit)) -> BaseGateC,
    {
        let mut circ = self.circ.borrow_mut();
        let bits = obj.as_bits(&self.st.env);

        if let Some(mut f) = quant {
            for (idx, qbit) in bits.qbits.iter().enumerate() {
                // NOTE: these copies shouldn't be necessary--this will be fixed
                // when arrays become iterable in Rust 2021.
                let gate = f((idx, *qbit));
                circ.push_qgate(gate, &self.st);
            }
        }

        if let Some(mut g) = class {
            for (idx, cbit) in bits.cbits.iter().enumerate() {
                let gate = g((idx, *cbit));
                circ.push_cgate(gate, &self.st);
            }
        }
    }

    /// Map two-bit classical and quantum gates over an allocation
    fn mapgate_pair<'a, A, B, Q, C, GQ, GC>(
        &'a mut self,
        fst: &A,
        snd: &B,
        quant: Option<Q>,
        class: Option<C>,
    ) where
        A: AsBits,
        B: AsBits,
        Q: FnMut((usize, Qbit, Qbit)) -> GQ,
        C: FnMut((usize, Cbit, Cbit)) -> GC,
        GateQ: From<GQ>,
        GateC: From<GC>,
    {
        let mut circ = self.circ.borrow_mut();

        let fst_bits = fst.as_bits(&self.st.env);
        let snd_bits = snd.as_bits(&self.st.env);

        if let Some(mut f) = quant {
            for ((idx, fst_qbit), snd_qbit) in
                fst_bits.qbits.iter().enumerate().zip(snd_bits.qbits.iter())
            {
                let gate = f((idx, *fst_qbit, *snd_qbit));
                circ.push_qgate(gate, &self.st);
            }
        }

        if let Some(mut g) = class {
            for ((idx, fst_cbit), snd_cbit) in
                fst_bits.cbits.iter().enumerate().zip(snd_bits.cbits.iter())
            {
                let gate = g((idx, *fst_cbit, *snd_cbit));
                circ.push_cgate(gate, &self.st);
            }
        }
    }

    /// Map two-bit classical-quantum gates over a pair of allocations. Unlike
    /// the previous two-allocation mapping function, this one has a definite
    /// direction: `ctrl` controls `snd`.
    fn mapgate_class_ctrl<'a, A, B, F>(&'a mut self, ctrl: &A, tgt: &B, f: Option<F>)
    where
        A: AsBits,
        B: AsBits,
        F: FnMut((usize, Cbit, Qbit)) -> BaseGateQ,
    {
        let mut circ = self.circ.borrow_mut();

        let ctrl_bits = ctrl.as_bits(&self.st.env);
        let tgt_bits = tgt.as_bits(&self.st.env);

        if let Some(mut f) = f {
            for ((idx, ctrl_bit), tgt_bit) in ctrl_bits
                .cbits
                .iter()
                .enumerate()
                .zip(tgt_bits.qbits.iter())
            {
                let gate = f((idx, *ctrl_bit, *tgt_bit));
                let mut gate = <GateC>::from(gate);
                gate.ctrls.push(*ctrl_bit);
                circ.push_cgate(gate, &self.st);
            }
        }
    }

    /// Free an allocation, calling a closure to determine how to free each bit.
    fn map_free<'a, B, Q, C>(&'a mut self, obj: &B, mut quant: Q, mut class: C)
    where
        B: AsBits,
        Q: FnMut((usize, Qbit)) -> FreeState,
        C: FnMut((usize, Cbit)) -> FreeState,
    {
        let bits = obj.as_bits(&self.st.env);
        let mut circ = self.circ.borrow_mut();

        for (idx, qbit) in bits.qbits.iter().enumerate() {
            circ.free_qbit(*qbit, quant((idx, *qbit)));
        }

        for (idx, cbit) in bits.cbits.iter().enumerate() {
            circ.free_cbit(*cbit, class((idx, *cbit)));
        }
    }
}

mod util {
    //! Some helper functions

    /// Construct a teed-off closure from an ordinary one.
    pub fn tee<'s, IT, T, F, A>(f: F, sink: &'s mut Vec<T>) -> impl FnMut(A) -> IT + 's
    where
        F: Fn(A) -> IT + 's,
        T: From<IT>,
        IT: Clone,
    {
        move |a| {
            let val = f(a);
            sink.push(val.clone().into());
            val
        }
    }
}
