# sv-parser
A parser library for System Verilog.

## Implementation Status

| Category                          | Module                                | Type | Parser | Test |
| --------------------------------- | ------------------------------------- | ---- | ------ | ---- |
| source_text                       | library_source_text                   | x    | x      | x    |
| source_text                       | system_verilog_source_text            | x    | x      |      |
| source_text                       | module_parameters_and_ports           | x    | x      |      |
| source_text                       | module_items                          | x    | x      |      |
| source_text                       | configuration_source_text             | x    | x      |      |
| source_text                       | interface_items                       | x    | x      |      |
| source_text                       | program_items                         | x    | x      |      |
| source_text                       | checker_items                         | x    | x      |      |
| source_text                       | class_items                           | x    | x      |      |
| source_text                       | constraints                           | x    | x      |      |
| source_text                       | package_items                         | x    | x      |      |
| declaration                       | module_parameter_declarations         | x    | x      |      |
| declaration                       | port_declarations                     | x    | x      |      |
| declaration                       | type_declarations                     | x    | x      |      |
| declaration                       | net_and_variable_types                | x    | x      |      |
| declaration                       | strengths                             | x    | x      | x    |
| declaration                       | delays                                | x    | x      |      |
| declaration                       | declaration_lists                     | x    | x      |      |
| declaration                       | declaration_assignments               | x    | x      |      |
| declaration                       | declaration_ranges                    | x    | x      |      |
| declaration                       | function_declarations                 | x    | x      |      |
| declaration                       | task_declarations                     | x    | x      |      |
| declaration                       | block_item_declarations               | x    | x      |      |
| declaration                       | interface_declarations                | x    | x      |      |
| declaration                       | assertion_declarations                | x    |        |      |
| declaration                       | covergroup_declarations               |      |        |      |
| declaration                       | let_declarations                      |      |        |      |
| primitive_instance                | primitive_instantiation_and_instances | x    | x      |      |
| primitive_instance                | primitive_strengths                   | x    | x      | x    |
| primitive_instance                | primitive_terminals                   | x    | x      |      |
| primitive_instance                | primitive_gate_and_switch_types       | x    | x      | x    |
| instantiations                    | module_instantiation                  | x    | x      |      |
| instantiations                    | interface_instantiation               | x    | x      |      |
| instantiations                    | program_instantiation                 | x    | x      |      |
| instantiations                    | checker_instantiation                 | x    | x      |      |
| instantiations                    | generated_instantiation               | x    | x      |      |
| udp_declaration_and_instantiation | udp_declaration                       |      |        |      |
| udp_declaration_and_instantiation | udp_ports                             |      |        |      |
| udp_declaration_and_instantiation | udp_body                              |      |        |      |
| udp_declaration_and_instantiation | udp_instantiation                     |      |        |      |
| behavioral_statements             | continuous_assignment_and_net_alias   | x    | x      |      |
| behavioral_statements             | procedural_blocks_and_assignments     | x    | x      |      |
| behavioral_statements             | parallel_and_sequential_blocks        | x    | x      |      |
| behavioral_statements             | statements                            | x    | x      |      |
| behavioral_statements             | timing_control_statements             | x    | x      |      |
| behavioral_statements             | conditional_statements                | x    | x      |      |
| behavioral_statements             | case_statements                       | x    | x      |      |
| behavioral_statements             | patterns                              | x    | x      |      |
| behavioral_statements             | looping_statements                    | x    | x      |      |
| behavioral_statements             | subroutine_call_statements            | x    | x      |      |
| behavioral_statements             | assertion_statements                  | x    | x      |      |
| behavioral_statements             | clocking_block                        | x    | x      |      |
| behavioral_statements             | randsequence                          | x    | x      |      |
| specify_section                   | specify_block_declaration             |      |        |      |
| specify_section                   | specify_path_declarations             |      |        |      |
| specify_section                   | specify_block_terminals               |      |        |      |
| specify_section                   | specify_path_delays                   |      |        |      |
| specify_section                   | system_timing_check_commands          |      |        |      |
| specify_section                   | system_timing_check_command_arguments |      |        |      |
| specify_section                   | system_timing_check_event_definitions |      |        |      |
| expressions                       | concatenations                        | x    | x      |      |
| expressions                       | subroutine_calls                      | x    | x      |      |
| expressions                       | expressions                           | x    | x      |      |
| expressions                       | primaries                             | x    | x      |      |
| expressions                       | expression_leftside_values            | x    | x      |      |
| expressions                       | operators                             | x    | x      | x    |
| expressions                       | numbers                               | x    | x      | x    |
| expressions                       | strings                               | x    | x      | x    |
| general                           | attributes                            | x    | x      | x    |
| general                           | comments                              | x    | x      | x    |
| general                           | identifiers                           | x    | x      | x    |
