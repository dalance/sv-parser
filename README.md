# sv-parser
A parser library for System Verilog.

## Implementation Status

| Category                          | Module                                | Type | Parser | Test |
| --------------------------------- | ------------------------------------- | ---- | ------ | ---- |
| source_text                       | library_source_text                   | x    | x      | x    |
| source_text                       | system_verilog_source_text            | x    | x      |      |
| source_text                       | module_parameters_and_ports           |      |        |      |
| source_text                       | module_items                          |      |        |      |
| source_text                       | configuration_source_text             |      |        |      |
| source_text                       | interface_items                       |      |        |      |
| source_text                       | program_items                         |      |        |      |
| source_text                       | checker_items                         |      |        |      |
| source_text                       | class_items                           |      |        |      |
| source_text                       | constraints                           |      |        |      |
| source_text                       | package_items                         |      |        |      |
| declaration                       | module_parameter_declarations         |      |        |      |
| declaration                       | port_declarations                     |      |        |      |
| declaration                       | type_declarations                     |      |        |      |
| declaration                       | net_and_variable_types                |      |        |      |
| declaration                       | strengths                             |      |        |      |
| declaration                       | delays                                |      |        |      |
| declaration                       | declaration_lists                     |      |        |      |
| declaration                       | declaration_assignments               |      |        |      |
| declaration                       | declaration_ranges                    |      |        |      |
| declaration                       | function_declarations                 |      |        |      |
| declaration                       | task_declarations                     |      |        |      |
| declaration                       | block_item_declarations               |      |        |      |
| declaration                       | interface_declarations                |      |        |      |
| declaration                       | assertion_declarations                |      |        |      |
| declaration                       | covergroup_declarations               |      |        |      |
| declaration                       | let_declarations                      |      |        |      |
| primitive_instance                | primitive_instantiation_and_instances |      |        |      |
| primitive_instance                | primitive_strengths                   |      |        |      |
| primitive_instance                | primitive_terminals                   |      |        |      |
| primitive_instance                | primitive_gate_and_switch_types       |      |        |      |
| instantiations                    | module_instantiation                  | x    | x      |      |
| instantiations                    | interface_instantiation               | x    | x      |      |
| instantiations                    | program_instantiation                 | x    | x      |      |
| instantiations                    | checker_instantiation                 | x    | x      |      |
| instantiations                    | generated_instantiation               |      |        |      |
| udp_declaration_and_instantiation | udp_declaration                       |      |        |      |
| udp_declaration_and_instantiation | udp_ports                             |      |        |      |
| udp_declaration_and_instantiation | udp_body                              |      |        |      |
| udp_declaration_and_instantiation | udp_instantiation                     |      |        |      |
| behavioral_statements             | continuous_assignment_and_net_alias   |      |        |      |
| behavioral_statements             | procedural_blocks_and_assignments     |      |        |      |
| behavioral_statements             | parallel_and_sequential_blocks        |      |        |      |
| behavioral_statements             | statements                            |      |        |      |
| behavioral_statements             | timing_control_statements             |      |        |      |
| behavioral_statements             | conditional_statements                |      |        |      |
| behavioral_statements             | case_statements                       |      |        |      |
| behavioral_statements             | patterns                              |      |        |      |
| behavioral_statements             | looping_statements                    |      |        |      |
| behavioral_statements             | subroutine_call_statements            |      |        |      |
| behavioral_statements             | assertion_statements                  |      |        |      |
| behavioral_statements             | clocking_block                        |      |        |      |
| behavioral_statements             | randsequence                          |      |        |      |
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
