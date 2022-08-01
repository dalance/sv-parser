// IEEE1800-2017 Clause 22.9
// The directive `unconnected_drive takes one of two arguments - pull1 or
// pull 0. When pull1 is specified, unconnected ports are pulled down. It is
// advisable to pair each `unconnected_drive with a
// `nounconnected_drive, but it is not required. The latest occurrence of
// either directive in the source controls what happens to unconnected ports.
// These directives shall be specified outside the design element declarations.
// The `resetall directive includes the effects of a `nounconnected
// directive.
`unconnected_drive pull0
`unconnected_drive pull1
`nounconnected_drive
// This file should be emitted from the preprocessor unchanged.
