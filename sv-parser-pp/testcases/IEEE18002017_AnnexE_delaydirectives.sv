/*
The compiler directives described in this annex are for informative purposes only and are not part of this
standard.
This annex describes additional compiler directives as companions to the compiler directives described in
Clause 22. The compiler directives described in this annex may not be available in all implementations of
SystemVerilog. The following compiler directives are described in this annex:
*/

//not supported:
// `default_decay_time 1.3 //[E.2]
// `defualt_decay_time 5
// `default_decay_time infinite
// `default_trireg_strength 100 //[E.3]

`delay_mode_distributed //[E.4]
`delay_mode_path //[E.5]
`delay_mode_unit //[E.6]
`delay_mode_zero //[E.7]