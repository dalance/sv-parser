
// Unusual case where a preprocessor comment (same symbol as a single-line
// comment, "//") is embedded in an emitted C-style comment.
// This should not preprocess, but not parse, i.e. in the emitted text, there
// will be an opening // C-style comment symbol "/*" but no closing symbol "*/".
`define A \
  A1 \
  A2 /* emitted */ \
  A3 /* // not emitted, unclosed C comment */ \
  A4

// Same as A, but without space before "//".
// This may catch bad parsers where the first "/" in "//" is treated as part of
// the closing "*/".
`define B \
  B1 \
  B2 /* emitted */ \
  B3 /*// not emitted, unclosed C comment */ \
  B4

// Another variation on B.
`define C \
  C1 \
  C2 /* emitted */ \
  C3 //* not emitted, C comment is closed */ \
  C4

// Another variation on B.
`define D \
  D1 \
  D2 /* emitted */ \
  D3 /* emitted, unclosed C comment *// \
  D4

`A

`B

`C

`D

