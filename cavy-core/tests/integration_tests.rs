//! This file contains, unsurprisingly, integration tests for the Cavy compiler.
//! Currently, all of these simply check whether correct (resp. incorrect) code
//! compiles (resp. FAILs to compile).

use cavy_core::{compile, context, session, util::FmtWith};

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
                let mut stats = session::Statistics::new();
                let mut conf = session::Config::default();
                $(conf.phase_config.last_phase = session::Phase::$phase;)?
                let mut ctx = context::Context::new(&conf, &mut stats);
                let id = ctx.srcs.insert_input(&stringify!($($src)*));
                let circ = compile::compile_circuit(id, &mut ctx);
                if let Err(errs) = circ {
                    eprintln!("{}", errs.fmt_with(&ctx));
                    panic!();
                }
            }
        )*
    };
}

macro_rules! is_fail {
    (FAIL) => {};
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
    no_main FAIL {
        fn f() {}
    }

    two_mains FAIL {
        fn main() {}
        fn main() {}
    }

    main_returns FAIL [Typecheck] {
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

    return_wrong_type FAIL {
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

    return_empty_wrong_type FAIL [Typecheck] {
        fn main() { }
        fn f() -> bool { }
    }

    double_move FAIL [Analysis] {
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

    field_access_binds_tightly [Analysis] {
        fn main() {
            let x = (4u8, 111u8);
            let y: ?u8 = ?x.0;
        }
    }

    move_from_tuple_fine_grained [Analysis] {
        fn main() {
            let pair = (?true, ?true);
            let x = pair.0;
            let y = pair.1;
        }
    }

    prev_partial_move_tuple FAIL [Analysis] {
        fn main() {
            let pair = (?true, ?true);
            let x = pair.0;
            let y = pair;
        }
    }

    prev_classical_partial_move_tuple [Analysis] {
        fn main() {
            let pair = (true, ?true);
            let x = pair.0;
            let y = pair;
        }
    }

    later_partial_move_tuple FAIL [Analysis] {
        fn main() {
            let pair = (?true, ?true);
            let y = pair;
            let x = pair.0;
        }
    }

    partial_move_tuple_nested FAIL [Analysis] {
        fn main() {
            let pair = (?true, (?true, ?false));
            let x = pair.1;
            let y = pair;
        }
    }

    partial_move_tuple_nested_2 FAIL [Analysis] {
        fn main() {
            let pair = (?true, (?true, ?false));
            let x = pair.1.1;
            let y = pair;
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

    recursion FAIL [Analysis] {
        fn main() { main() }
    }

    mutual_recursion FAIL [Analysis] {
        fn main() {}
        fn f() { g() }
        fn g() { f() }
    }

    classical_feedback FAIL [Analysis] {
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

    linear_conditional [Analysis] {
        fn main() {
            let x: u32;
            if &?true { x = 3; } else { x = 4; }
        }
    }

    conditional_wrong_type FAIL {
        fn main() {
            let x: u32;
            if 56 { x = 3; } else { x = 4; }
        }
    }

    sub_lin_cond_meas FAIL {
        fn main() {
            let x = ?false;
            let y = ?true;
            if &y {
                let c = !x;
            }
        }
    }

    sub_lin_cond_meas_call FAIL {
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

    assn_from_cond [Analysis] {
        fn main() {
            let x = ?true;
            let y = if &x {
                ?true
            } else {
                ?false
            };
        }
    }

    if_incompatible_types FAIL {
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

    create_tuple_binop [Typecheck] {
        fn main() {
            let t = (true, 1 + 2);
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

    no_bare_struct_in_cond FAIL [Typecheck] {
        struct A {}

        fn main() {
            if A {} {}
        }
    }

    const_prop_linear_struct_field [Optimization] {
        struct MyStruct {
            a: u32,
            b: ?bool,
        }

        fn main() {
            let x = MyStruct {
                a: 14,
                b: ?true,
            };
            let q = x.b;
        }
    }

    parse_enum_simple [Parse] {
        enum MyEnum {
            A,
            B,
        }
    }

    nested_function {
        fn main() {
            let x = ?false;
            fn f(x: ?bool) -> ?bool {
                ~x
            }
            let y = f(x);
        }
    }

    // CLASSICAL CONTROL

    class_under_quant_contr FAIL [Analysis] {
        fn main() {
            let b = false;
            let &q = ?true;
            if q {
                b = ~b;
            }
        }
    }

    // UNSAFE

    unsafe_fn [Parse] {
        fn main() {
            unsafe { f(); }
        }

        unsafe fn f() {}
    }

    unsafe_non_block FAIL [Parse] {
        fn main() {
            let y = unsafe 2;
        }
    }

    unsafe_fn_block FAIL [Parse] {
        fn f() unsafe {}
    }

    unsafe_bare_assert FAIL [Analysis] {
        fn main() {
            assert 0;
        }
    }

    unsafe_wrapped_assert [Analysis] {
        fn main() {
            unsafe { assert 0; }
        }
    }

    unsafe_bare_fn_call FAIL [Analysis] {
        unsafe fn f() {
            assert 3;
        }

        fn main() {
            f()
        }
    }

    unsafe_wrapped_fn_call [Analysis] {
        unsafe fn f() {
            assert 3;
        }

        fn main() {
            unsafe { f() }
        }
    }

    // BORROW

    borrow_lower [Typecheck] {
        fn main() {
            let x = ?true;
            let y = &x;
            let z = y;
        }
    }

    lifetime_in_borrow FAIL [Typecheck] {
        fn main() {
            let x = ?true;
            let y = &'a x;
        }
    }

    // Operators on borrowed types

    or_takes_shrd [Typecheck] {
        fn main() {
            let x = ?true;
            let y = ?false;
            let z = &x || &y;
            let test: &?bool = z;
        }
    }

    swap_takes_mut [Typecheck] {
        fn main() {
            let x = ?true;
            let y = ?true;
            &mut x $ &mut y;
        }
    }

    assn_or_not_quantum FAIL [Typecheck] {
        fn main() {
            let x = ?true;
            let y = ?true;
            x |= &y;
        }
    }

    // Borrow checking

    double_borrow [Analysis] {
        fn main() {
            let w = ?true;
            let x = &w;
            let y = &w;
            let z = x;
        }
    }

    shrd_borrow_after_uniq_borrow [Analysis] {
        fn main() {
            let w = ?false;
            let x = &mut w;
            let y = &w;
        }
    }

    shrd_borrow_during_uniq_borrow FAIL [Analysis] {
        fn main() {
            let w = ?false;
            let x = &mut x;
            let y = &w;
            let z = x;
        }
    }

    return_param_borrow [Analysis] {
        fn main() {}

        fn g(x: &?bool) -> &?bool {
            x
        }
    }

    return_local_borrow FAIL [Analysis] {
        fn main() {}

        fn g() -> &?bool {
            let x = ?false;
            let y = &x;
            y
        }
    }

    borrow_from_moved FAIL [Analysis] {
        fn main() {
            let x = ?false;
            let y = x;
            let r = &x;
        }
    }

    move_from_borrow FAIL [Analysis] {
        fn main() {
            let x = ?false;
            let y = &x;
            z = x;
            snd = y;
        }
    }

    deref_once [Analysis] {
        fn main() {
            let x = &mut ?false;
            let a = *x;
            *x = a;
        }
    }

    deref_not_replaced FAIL [Analysis] {
        fn main() {
            let x = &mut ?false;
            let a = *x;
        }
    }

    deref_borrow_twice FAIL [Analysis] {
        fn main() {
            let x = &mut ?false;
            let a = *x;
            let b = *x;
        }
    }

    move_borrowed_after_deref FAIL [Analysis] {
        fn main() {
            let x = ?false;
            let r = &mut x;
            let y = *r;
            let x = x;
        }
    }

    assign_to_shrd_ref FAIL [Analysis] {
        fn main() {
            let x = ?false;
            let y = ?false;
            let r = &x;
            r = &y;
        }
    }
}
