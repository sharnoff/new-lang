// #![allow(unused_variables)]
// #![allow(dead_code)]

use futures::executor::block_on;
use hydra::JobId;

mod ast;
mod db;
mod db_new;
mod error;
mod token_tree;
mod tokens;
mod utils;

use db::Files;

fn main() {
    let db = db_new::Database::new();

    let job = JobId::initial_seed();
    let ast = block_on(db.get_ast_info(job, "test_input.tc".into()));
    println!("{:?}", ast);

    /*
    let mut files = Files::new();

    files.reserve("test_input.tc");

    let test_input_file = files.file("test_input.tc");
    let ast = test_input_file.get_ast(|err| panic!("Failed to open file: {:?}", err));

    println!("{:?}", std::ops::Deref::deref(&ast));

    drop(ast);
    drop(test_input_file);

    let num_errors = files.print_errors();
    if num_errors != 0 {
        let num_err_str = match num_errors {
            1 => "a previous error".into(),
            n => format!("{} previous errors", n),
        };

        eprintln!(
            "{}: Failed due to {}",
            error::ERR_COLOR.paint("error"),
            num_err_str
        );
    }
    */
}
