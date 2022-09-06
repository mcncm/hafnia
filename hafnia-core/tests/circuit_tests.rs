#[macro_use]
mod circuit;

use hafnia_core::circuit::BaseGateQ;

use BaseGateQ::*;

test_unitary! {
    x_gate {
        fn main() {
            let x = ?true;
        }
    } => [
        X(0.into())
    ]

    invert_borrow_null {
        fn main() {
            let x = ?false;
            let ref = ~&x;
        }
    } => []

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
