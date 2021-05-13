//! In this file I'll keep my trophies: previous bugged examples that now
//! compile (or fail to compile) correctly. Also, known bugs that haven't been
//! fixed yet.

#[macro_use]
mod common;

test_compiles! {
    /*
    FOUND: 2021-05-12
    FIXED: 2021-05-12
    */
    u2_parses {
        fn main () { let x: u2 = 1u2; }
    }

    /*
    FOUND: 2021-05-12
    FIXED: 2021-05-12
    */
    const_prop_tuple {
        fn main() {
            let x = (?false, true);
            x.0 = ~x.0;
        }
    }

    /*
    FOUND: 2021-05-12
    FIXED:
    */
    return_place_linearity {
        fn main() {
            let var = ?47u8;
            var = f(var);
            let num = !var;
            io num -> my_number;
        }

        fn f(number: ?u8) -> ?u8 {
            number = #number;
            ~number
        }
    }
}
