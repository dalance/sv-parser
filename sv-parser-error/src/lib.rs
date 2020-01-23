use std::path::PathBuf;
use thiserror::Error;

// -----------------------------------------------------------------------------

#[derive(Error, Debug)]
pub enum Error {
    #[error("IO error")]
    Io(#[from] std::io::Error),
    #[error("File error: {path:?}")]
    File {
        #[source]
        source: std::io::Error,
        path: PathBuf,
    },
    #[error("Include error")]
    Include {
        #[from]
        source: Box<Error>,
    },
    #[error("Parse error: {0:?}")]
    Parse(Option<(PathBuf, usize)>),
    #[error("Preprocess error")]
    Preprocess,
    #[error("Define argument not found: {0}")]
    DefineArgNotFound(String),
    #[error("Define not found: {0}")]
    DefineNotFound(String),
    #[error("Define must have argument")]
    DefineNoArgs,
    #[error("Exceed recursive limit")]
    ExceedRecursiveLimit,
    #[error("Include line can't have other items")]
    IncludeLine,
}
