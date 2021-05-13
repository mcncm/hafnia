//! In this file I'll keep my trophies: previous bugged examples that now
//! compile (or fail to compile) correctly. Also, known bugs that haven't been
//! fixed yet.

#[macro_use]
mod common;

test_compiles! {
    /*
    FOUND: 2021-05-12
    FIXED: 2021-05-12
    CAUSE: Never implemented
    */
    u2_parses {
        fn main () { let x: u2 = 1u2; }
    }

    /*
    FOUND: 2021-05-12
    FIXED: 2021-05-12
    CAUSE: Incorrect `Value::Unit` default value in values tree.
    */
    const_prop_tuple {
        fn main() {
            let x = (?false, true);
            x.0 = ~x.0;
        }
    }

    /*
    FOUND: 2021-05-12
    FIXED: 2021-05-13
    CAUSE: Dataflow framework statements misordered due to breaking up transfer
           functions into `pre` and `post` components.
    */
    return_place_linearity {
        fn main() {
            let var = ?47u8;
            var = f(var);
            let num = !var;
        }

        fn f(number: ?u8) -> ?u8 {
            ~number
        }
    }
}
