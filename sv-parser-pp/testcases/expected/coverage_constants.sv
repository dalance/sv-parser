// IEEE1800-2017 Clause 40.3.1
// The following predefined `define macros represent basic real-time coverage
// capabilities accessible directly from SystemVerilog:

// Coverage control
localparam int SV_COV_START = 0; // 0
localparam int SV_COV_STOP  = 1; // 1
localparam int SV_COV_RESET = 2; // 2
localparam int SV_COV_CHECK = 3; // 3

// Scope definition (hierarchy traversal/accumulation type)
localparam int SV_COV_MODULE = 10; // 10
localparam int SV_COV_HIER   = 11; // 11

// Coverage type identification
localparam int SV_COV_ASSERTION = 20; // 20
localparam int SV_COV_FSM_STATE = 21; // 21
localparam int SV_COV_STATEMENT = 22; // 22
localparam int SV_COV_TOGGLE    = 23; // 23

// Status results
localparam int SV_COV_OVERFLOW = -2; // -2
localparam int SV_COV_ERROR    = -1; // -1
localparam int SV_COV_NOCOV    = 0; // 0
localparam int SV_COV_OK       = 1; // 1
localparam int SV_COV_PARTIAL  = 2; // 2
