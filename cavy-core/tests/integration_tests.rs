//! This file contains, unsurprisingly, integration tests for the Cavy compiler.
//! Currently, all of these simply check whether correct (resp. incorrect) code
//! compiles (resp. fails to compile).

use cavy_core::{compile, context, session};

/// This simple macro builds compilation tests. It's not very fine-grained, so
/// you can't e.g. test the diagnostic.
macro_rules! test_compiles {
    ($($name:ident $($x:ident)? { $($src:tt)* })*) => {
        $(
            $(is_fail!{$x} #[should_panic])?
            #[test]
            pub fn $name() {
                // This is identical to the current stand-in `cavy` macro in
                // cavy/lib.rs. We can't necessarily use that macro, though,
                // because I want access to the config. Maybe it should *return*
                // the config? Not clear. Good enough for now.
                let conf = session::Config::default();
                let mut ctx = context::Context::new(&conf);
                let id = ctx.srcs.insert_input(&stringify!($($src)*));
                let circ = compile::compile_circuit(id, &mut ctx);
                if let Err(errs) = circ {
                    eprintln!("{}", context::CtxDisplay::fmt_with(&errs, &ctx));
                    panic!();
                }
            }
        )*
    };
}

macro_rules! is_fail {
    (fail) => {};
}

test_compiles! {
    empty_main {
        fn main() {}
    }

    // A previous bug would report this as a second function named `main`
    function_after_main {
        fn main() {}
        fn f() {}
    }

    // this one is a little dubious! It's here to test the behavior of the
    // compiler; it's not necessarily expressing the behavior we *want*.
    no_main fail {
        fn f() {}
    }

    two_mains fail {
        fn main() {}
        fn main() {}
    }

    function_call {
        fn f() { }
        fn main() { f() }
    }

    return_constant {
        fn f() -> u32 { 12 }
        fn main() { let x = f(); }
    }

    return_wrong_type fail {
        fn main() { }
        fn f() -> u32 { true }
    }

    return_assigned {
        fn main() { let x = f(); }
        fn f() -> u32 {
            let x = 12;
            x
        }
    }

    double_move fail {
        fn main() {
            let x = ?false;
            let y = x;
            let z = x;
        }
    }

    chained_move {
        fn main() {
            let x = ?false;
            let y = x;
            let z = y;
        }
    }

    recursion fail {
        fn main() { main() }
    }

    mutual_recursion fail {
        fn main() {}
        fn f() { g() }
        fn g() { f() }
    }

    classical_feedback fail {
        fn main() {
            let q = ?true;
            let c = !q;
            let r = ?c;
        }
    }

    simple_conditional {
        fn main() {
            let x: u32;
            if true { x = 3; } else { x = 4; }
        }
    }

    linear_conditional {
        fn main() {
            let x: u32;
            if ?true { x = 3; } else { x = 4; }
        }
    }

    conditional_wrong_type fail {
        fn main() {
            let x: u32;
            if 56 { x = 3; } else { x = 4; }
        }
    }

    sub_lin_cond_meas fail {
        fn main() {
            let x = ?false;
            let y = ?true;
            if y {
                let c = !x;
            }
        }
    }

    sub_lin_cond_meas_call fail {
        fn main() {
            let x = ?false;
            let y = ?true;
            if y {
                let c = f(x);
            }
        }

        fn f(x: ?bool) -> bool {
            g(x)
        }

        fn g(x: ?bool) -> bool {
            !x
        }
    }

    assn_from_cond {
        fn main() {
            let x = ?true;
            let y = if x {
                ?true
            } else {
                ?false
            };
        }
    }

    if_incompatible_types fail {
        fn main() {
            let x = if true {
                true
            } else {
                3u8
            };
        }
    }
}
