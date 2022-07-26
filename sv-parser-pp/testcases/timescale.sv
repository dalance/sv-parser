// IEEE1800-2017 Clause 22.7
// This directive specifies the time unit and time precision of the design
// elements that follow it. The time unit is the unit of measurement for time
// values such as the simulation time and delay values.
// The `timescale compiler directive specifies the default unit of measurement
// for time and delay values and the degree of accuracy for delays in all
// design elements that follow this directive, and that do not have timeunit
// and timeprecision constructs specified within the design element, until
// another `timescale compiler directive is read.
// The integers in these arguments specify an order of magnitude for the size
// of the value; the valid integers are 1, 10, and 100.
// The character strings represent units of measurement; the valid character
// strings are s, ms, us, ns, ps, and fs.
`timescale 1 s / 10 ms
`timescale 10 us / 100 ns
`timescale 100 ps / 100 fs
// This file should be emitted from the preprocessor unchanged.
