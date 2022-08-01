/* IEEE1800-2017 Clause 22.5.1, page 676
If a one-line comment (that is, a comment specified with the characters //) is
included in the text, then the comment shall not become part of the substituted
text.
*/

// A has no comment
// B has a comment after 1 space
// C has a comment after 3 spaces
`define A 11
`define B 22 // Comment not included in macro, but whitespace before `//` is.
`define C 33   // Comment not included in macro, but whitespace before `//` is.

interface A #(p=`A) (); endinterface
interface B #(p=`B) (); endinterface
interface C #(p=`C) (); endinterface
