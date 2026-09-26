//! Error types for `sv-parser` and its helper crates.
//!
//! This crate defines [`Error`], the centralized error enumeration representing
//! failures that can happen during file reading, UTF-8 decoding, preprocessing
//! (macro expansion, include resolution, recursion limits), and parsing.

use std::path::PathBuf;
use thiserror::Error;

// -----------------------------------------------------------------------------

/// Represents all possible errors that can occur during preprocessing and parsing
/// SystemVerilog source files.
#[derive(Error, Debug)]
pub enum Error {
    /// Generic I/O error encountered during file operations.
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    /// File access error for a specific file path.
    #[error("File error: {path:?}")]
    File {
        /// The underlying I/O error.
        #[source]
        source: std::io::Error,
        /// The path of the file that could not be accessed.
        path: PathBuf,
    },

    /// The specified file could not be decoded as valid UTF-8.
    #[error("File could not be read as UTF8: {0:?}")]
    ReadUtf8(PathBuf),

    /// Error encountered while processing an included file (e.g., via `` `include ``).
    #[error("Include error")]
    Include {
        /// The boxed inner error causing the include failure.
        #[from]
        source: Box<Error>,
    },

    /// Syntax parsing error.
    ///
    /// Contains an optional tuple of `(PathBuf, usize)` indicating the original
    /// file path and byte offset where parsing failed, resolved back to the
    /// original source location before preprocessing.
    #[error("Parse error: {0:?}")]
    Parse(Option<(PathBuf, usize)>),

    /// Preprocessing error.
    ///
    /// Contains an optional tuple of `(PathBuf, usize)` indicating the source file
    /// path and byte offset where preprocessing failed.
    #[error("Preprocess error: {0:?}")]
    Preprocess(Option<(PathBuf, usize)>),

    /// A macro call was missing a required argument.
    ///
    /// Contains the name of the missing argument.
    #[error("Define argument not found: {0}")]
    DefineArgNotFound(String),

    /// A macro identifier was referenced (e.g., `` `NAME ``) but was never defined.
    ///
    /// Contains the name of the undefined macro.
    #[error("Define not found: {0}")]
    DefineNotFound(String),

    /// A macro that requires arguments was invoked without arguments.
    ///
    /// Contains the macro identifier.
    #[error("Define must have argument")]
    DefineNoArgs(String), // String is the macro identifier.

    /// The recursion depth limit (default 64) was exceeded during macro expansion
    /// or nested include file resolution.
    #[error("Exceed recursive limit")]
    ExceedRecursiveLimit,

    /// An `` `include `` directive line contained invalid trailing items on the same line.
    #[error("Include line can't have other items")]
    IncludeLine,
}
