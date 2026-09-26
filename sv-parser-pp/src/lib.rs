//! Preprocessor for SystemVerilog source code compliant with IEEE 1800-2017.
//!
//! This crate implements the preprocessing phase of the SystemVerilog compilation pipeline:
//!
//! - **Macro definition and expansion**: Handles `` `define ``, parameterless and parameterized
//!   macros, default argument values, stringification (`` `" ``), token concatenation (`` `` ``),
//!   and predefined macros (such as `` `__FILE__ ``, `` `__LINE__ ``, and coverage macros).
//! - **File inclusion**: Resolves `` `include `` directives with configurable include search paths.
//! - **Conditional compilation**: Evaluates `` `ifdef ``, `` `ifndef ``, `` `elsif ``, `` `else ``, and `` `endif `` blocks.
//! - **Source origin tracking**: Preserves mapping between preprocessed text byte offsets
//!   and their original source files and spans via [`range::Range`] and [`preprocess::PreprocessedText`].
//! - **Recursion guards**: Enforces recursion limits to prevent infinite loops during macro expansion
//!   or nested file inclusions.

#![allow(clippy::type_complexity)]
#![recursion_limit = "256"]

pub mod preprocess;
pub mod range;

