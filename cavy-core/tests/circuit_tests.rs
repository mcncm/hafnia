#[macro_use]
mod circuit;

use cavy_core::circuit::BaseGateQ;

use BaseGateQ::*;

use std::io::{self, Write};

test_unitary! {
    x_gate {
        fn main() {
            let x = ?true;
        }
    } => [
        X(0.into())
    ]

    simple_cnot_if {
        fn main() {
            let x = #?false;
            let y = ?false;
            if &x {
                y = ~y;
            }
        }
    } => [
        H(0.into()),
        Cnot { ctrl: 0.into(), tgt: 1.into() }
    ]
}
