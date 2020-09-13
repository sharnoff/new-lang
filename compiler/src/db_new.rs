//! An experimental new version of the database, using `hydra`
//!
//! Once merged, this module will fully replace [`db`](../db/index.html).

hydra::make_database! {
    /// The central database used for managing queries of every piece of information in the
    /// compiler
    struct Database impl {
        @single root_file: String,
        get_foo: Foo,
    }
}

#[hydra::query(Foo)]
async fn get_foo(db: Database, job: &hydra::JobId, key: usize) -> hydra::Result<f64> {
    Ok(key as f64 / usize::MAX as f64)
}
