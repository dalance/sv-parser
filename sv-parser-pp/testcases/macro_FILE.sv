// __FILE__ = `__FILE__

`ifdef __FILE__
// This block SHOULD be emitted from the preprocessor.
`elsif UNDEFINED
// NOT emitted.
`endif

`ifndef __FILE__
// This block should NOT be emitted from the preprocessor.
// However, following (conditional) definition should make it through the
// preprocessor parsing stage without error.
`define __FILE__ "(null)"
`elsif UNDEFINED
// Emitted instead.
`endif

// The following define should have no effect.
`define __FILE__ "FOO"

// The following undef should have no effect.
`undef __FILE__

// NOTE: Comparison against expected value are destined to fail in testcase.
