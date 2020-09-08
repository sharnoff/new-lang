//! Testing for the parser
//!
//! Each function here is labeled with a trailing `_good` or `_bad` to indicate whether we're
//! expecting errors or not.

use super::*;
use crate::Files;

// A hack macro taken from https://stackoverflow.com/a/40234666
macro_rules! func_name {
    () => {{
        fn f() {}
        fn type_name_of<T>(_: T) -> &'static str {
            std::any::type_name::<T>()
        }
        let name = type_name_of(f);
        &name[..name.len() - 3]
    }};
}

#[test]
fn parse_fndecls_good() {
    let input_str = r#"
        fn foo() {
            print("bar")
        }

        fn get<ref a, T>(i: usize, ys: &|ref a| [T]) -> &|ref a| T {
            &ys[i]
        }
        "#;
    let name = func_name!();
    let files = Files::mock_single_file(name, input_str);
    let file = files.file(name);
    drop(file.get_ast(|_| unreachable!()));
    assert_eq!(0, files.print_errors());

    // TODO: Check that produced AST is as expected
}
