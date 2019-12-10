use failure::{Backtrace, Context, Fail};
use std::fmt;
use std::fmt::Display;
use std::io::Error as IOError;
use std::path::PathBuf;

// -----------------------------------------------------------------------------

#[derive(Fail, Debug)]
pub enum ErrorKind {
    #[fail(display = "IO error")]
    Io,
    #[fail(display = "File error: {:?}", _0)]
    File(PathBuf),
    #[fail(display = "Include error")]
    Include,
    #[fail(display = "Parse error: {:?}", _0)]
    Parse(Option<(PathBuf, usize)>),
    #[fail(display = "Preprocess error")]
    Preprocess,
    #[fail(display = "Define argument not found: {}", _0)]
    DefineArgNotFound(String),
    #[fail(display = "Define not found: {}", _0)]
    DefineNotFound(String),
    #[fail(display = "Define must have argument")]
    DefineNoArgs,
    #[fail(display = "Recursive define is detected: {}", _0)]
    DefineRecursive(String),
}

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct Error {
    inner: Context<ErrorKind>,
}

impl Fail for Error {
    fn cause(&self) -> Option<&dyn Fail> {
        self.inner.cause()
    }

    fn backtrace(&self) -> Option<&Backtrace> {
        self.inner.backtrace()
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Display::fmt(&self.inner, f)
    }
}

impl Error {
    pub fn new(inner: Context<ErrorKind>) -> Error {
        Error { inner }
    }

    pub fn kind(&self) -> &ErrorKind {
        self.inner.get_context()
    }
}

impl From<ErrorKind> for Error {
    fn from(kind: ErrorKind) -> Error {
        Error {
            inner: Context::new(kind),
        }
    }
}

impl From<Context<ErrorKind>> for Error {
    fn from(inner: Context<ErrorKind>) -> Error {
        Error { inner }
    }
}

// -----------------------------------------------------------------------------

impl From<IOError> for Error {
    fn from(error: IOError) -> Error {
        Error {
            inner: error.context(ErrorKind::Io),
        }
    }
}
