#![allow(unused_macros)]

/// This simple macro builds compilation tests. It's not very fine-grained, so
/// you can't e.g. test the diagnostic.
macro_rules! test_compiles {
    ($($name:ident $($x:ident)? $([$phase:ident])? { $($src:tt)* })*) => {
        $(
            $(is_fail!{$x} #[should_panic])?
            #[test]
            #[allow(unused_mut)]
            pub fn $name() {
                // This is identical to the current stand-in `hafnia` macro in
                // hafnia/lib.rs. We can't necessarily use that macro, though,
                // because I want access to the config. Maybe it should *return*
                // the config? Not clear. Good enough for now.
                let mut stats = hafnia_core::session::Statistics::new();
                let mut conf = hafnia_core::session::Config::default();
                $(conf.phase_config.last_phase = hafnia_core::session::Phase::$phase;)?
                let mut ctx = hafnia_core::context::Context::new(&conf, &mut stats);
                let id = ctx.srcs.insert_input(&stringify!($($src)*));
                let circ = hafnia_core::compile::compile_circuit(id, &mut ctx);
                if let Err(errs) = circ {
                    eprintln!("{}", hafnia_core::util::FmtWith::fmt_with(&errs, &ctx));
                    panic!();
                }
            }
        )*
    };
}

macro_rules! is_fail {
    (FAIL) => {};
}
