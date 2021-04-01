//! This file contains, unsurprisingly, integration tests for the Cavy compiler.
//! Currently, all of these simply check whether correct (resp. incorrect) code
//! compiles (resp. fails to compile).

use cavy_core::{compile, context, session};

/// This simple macro builds compilation tests. It's not very fine-grained, so
/// you can't e.g. test the diagnostic.
macro_rules! test_compiles {
    ($($name:ident $($x:ident)? $([$phase:ident])? { $($src:tt)* })*) => {
        $(
            $(is_fail!{$x} #[should_panic])?
            #[test]
            #[allow(unused_mut)]
            pub fn $name() {
                // This is identical to the current stand-in `cavy` macro in
                // cavy/lib.rs. We can't necessarily use that macro, though,
                // because I want access to the config. Maybe it should *return*
                // the config? Not clear. Good enough for now.
                let mut conf = session::Config::default();
                $(conf.phase_config.last_phase = session::Phase::$phase;)?
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

    main_returns fail [Typecheck] {
        fn main() { true }
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

    return_empty_wrong_type fail [Typecheck] {
        fn main() { }
        fn f() -> bool { }
    }

    double_move fail [Analysis] {
        fn main() {
            let x = ?false;
            let y = x;
            let z = x;
        }
    }

    double_move_self [Analysis] {
        fn main() {
            let y = ?false;
            y = y;
            y = y;
        }
    }

    move_from_tuple_fine_grained [Analysis] {
        fn main() {
            let pair = (?true, ?true);
            let x = pair.0;
            let y = pair.1;
        }
    }

    chained_move [Analysis] {
        fn main() {
            let x = ?false;
            let y = x;
            let z = y;
        }
    }

    move_after_shadow [Analysis] {
        fn main() {
            let x = false;
            let x = ?x;
            let y = x;
        }
    }

    recursion fail [Analysis] {
        fn main() { main() }
    }

    mutual_recursion fail [Analysis] {
        fn main() {}
        fn f() { g() }
        fn g() { f() }
    }

    classical_feedback fail [Analysis] {
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

    create_tuple {
        fn main() {
            let t = (0, ?true, (false, true));
        }
    }

    // TODO we have a ways to go: this doesn’t lower yet!
    create_struct [Parse] {
        struct A {
            a: u8,
            b: ?bool,
        }

        fn main() {
            let x = A {
                a: 3,
                b: ?true,
            };
        }
    }

    no_bare_struct_in_cond fail [Typecheck] {
        struct A {}

        fn main() {
            if A {} {}
        }
    }
}
