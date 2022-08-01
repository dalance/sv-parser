// IEEE1800-2017 Clause 22.10
// The directives `celldefine and `endcelldefine tag modules as cell modules.
// Cells are used by certain PLI routines and may be useful for applications
// such as delay calculations. It is advisable to pair each `celldefine with an
// `endcelldefine, but it is not required. The latest occurrence of either
// directive in the source controls whether modules are tagged as cell modules.
// More than one of these pairs may appear in a single source description.
// These directives may appear anywhere in the source description, but it is
// recommended that the directives be specified outside any design elements.
//  The `resetall directive includes the effects of a `endcelldefine directive.
`celldefine
`endcelldefine
// This file should be emitted from the preprocessor unchanged.
