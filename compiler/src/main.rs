// #![allow(unused_variables)]
// #![allow(dead_code)]

use futures::executor::block_on;
use hydra::JobId;

mod ast;
mod db;
mod error;
mod files;
mod token_tree;
mod tokens;
mod utils;

use db::Database;

fn main() {
    let db = Database::new();

    block_on(async {
        let job = JobId::initial_seed();
        let _ast = db.ast_info(job, "test_input.tc".into()).await;

        let errors = db.errors().await;
        let count = error::display_errors(&db, &JobId::initial_seed(), errors).await;

        if count == 0 {
            println!("Successfully parsed.");
        } else {
            let num_errs = match count {
                1 => "a previous error".into(),
                n => format!("{} previous errors", n),
            };

            eprintln!("{}: Failed due to {}", error::ERR_COLOR.paint("error"), num_errs);
        }
    })
}
