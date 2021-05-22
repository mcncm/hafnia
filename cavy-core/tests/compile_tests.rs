#[macro_use]
mod common;

test_compiles! {
    multiple_args {
        fn main() {
            let x = ?true;
            let y = ?true;
            let z = f(x, y);
        }

        fn f(x: ?bool, y: ?bool) -> ?bool {
            y
        }
    }
}
