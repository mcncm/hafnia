//! In this file I'll keep my trophies: previous bugged examples that now
//! compile (or fail to compile) correctly. Also, known bugs that haven't been
//! fixed yet.

#[macro_use]
mod common;

test_compiles! {
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
            let var: ?u32 = ?47;
            var = f(var);
            let num = !var;
        }

        fn f(number: ?u32) -> ?u32 {
            ~number
        }
    }

    /*
    FOUND: 2021-05-16
    FIXED: 2021-05-16
    CAUSE: in `sub_constr_loan`, was looking for lhs ascriptions from the *root*
           of the `Place`, not from the end.
    */
    pair_borrow {
        fn main() {
            let x = ?true;
            let y = ?true;
            let pair = (&x, &y);
        }
    }
}
