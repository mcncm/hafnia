//! This module handles the mir-level "optimizations", which are understood as
//! anything that mutates the Mir.

use crate::{context::Context, mir::Mir, session::Config};

/// Type of an optimization routine
type OptFn = dyn Fn(&mut Mir, &Context);

/// Type of a predicate guarding the application of an optimization
type GuardFn = dyn Fn(&Config) -> bool;

/// I'm a little macro, short and stout...
macro_rules! decl_opts {
    ($($name:ident : $level:expr,)*) => {
        // Is this a bad idea? I guess we'll see if this is a bad idea.
        $(mod $name;)*

        /// This static array holds the optimizations that may be applied,
        /// together with the conditions under which they are.
        #[rustfmt::skip]
        const OPTS: &'static [(&OptFn, &GuardFn)] = &[
            $((&$name::optimize as &OptFn, &|conf: &Config| {
                (conf.opt.level >= $level && conf.opt.flags.$name >= 0) ||
                    conf.opt.flags.$name == 1
            })),*
        ];

        /// A struct of optimization flags: 0 if "no preference", 1 if "override
        /// yes", -1 if "override no."
        #[derive(Default, Debug, PartialEq, Eq)]
        pub struct OptFlags {
            $($name: i8,)*
        }

        impl OptFlags {
            pub fn enable(&mut self, flag: &str) {
                match flag {
                    $(
                        stringify!($name) => self.$name = 1,
                    )*
                        _ => {}
                }
            }

            pub fn disable(&mut self, flag: &str) {
                match flag {
                    $(
                        stringify!($name) => self.$name = -1,
                    )*
                        _ => {}
                }
            }
        }
    };
}

// And this is where we actually declare the optimizations we wish to use,
// together with the optimization level at which they turn on.
decl_opts![
    constprop:  1,
    unipotence: 2,
];

/// Main entry point for the `opt` module
pub fn optimize(mir: &mut Mir, ctx: &Context) {
    for opt in OPTS.iter().filter_map(|opt| accept_opt(opt, ctx)) {
        opt(mir, ctx)
    }
}

/// Decide whether to apply an optimization based on the attached guard function
fn accept_opt<'f>(opt: &(&'f OptFn, &'f GuardFn), ctx: &Context) -> Option<&'f OptFn> {
    let cond = opt.1;
    if cond(ctx.conf) {
        Some(opt.0)
    } else {
        None
    }
}
