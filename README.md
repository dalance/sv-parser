# sv-parser
A parser library for System Verilog.

## Implementation Status

| Category                          | Module                                | SyntexTree | Parser |
| --------------------------------- | ------------------------------------- | ---------- | ------ |
| source_text                       | library_source_text                   | x          | x      |
| source_text                       | system_verilog_source_text            | x          | x      |
| source_text                       | module_parameters_and_ports           | x          | x      |
| source_text                       | module_items                          | x          | x      |
| source_text                       | configuration_source_text             | x          | x      |
| source_text                       | interface_items                       | x          | x      |
| source_text                       | program_items                         | x          | x      |
| source_text                       | checker_items                         | x          | x      |
| source_text                       | class_items                           | x          | x      |
| source_text                       | constraints                           | x          | x      |
| source_text                       | package_items                         | x          | x      |
| declaration                       | module_parameter_declarations         | x          | x      |
| declaration                       | port_declarations                     | x          | x      |
| declaration                       | type_declarations                     | x          | x      |
| declaration                       | net_and_variable_types                | x          | x      |
| declaration                       | strengths                             | x          | x      |
| declaration                       | delays                                | x          | x      |
| declaration                       | declaration_lists                     | x          | x      |
| declaration                       | declaration_assignments               | x          | x      |
| declaration                       | declaration_ranges                    | x          | x      |
| declaration                       | function_declarations                 | x          | x      |
| declaration                       | task_declarations                     | x          | x      |
| declaration                       | block_item_declarations               | x          | x      |
| declaration                       | interface_declarations                | x          | x      |
| declaration                       | assertion_declarations                | x          | x      |
| declaration                       | covergroup_declarations               | x          | x      |
| declaration                       | let_declarations                      | x          | x      |
| primitive_instance                | primitive_instantiation_and_instances | x          | x      |
| primitive_instance                | primitive_strengths                   | x          | x      |
| primitive_instance                | primitive_terminals                   | x          | x      |
| primitive_instance                | primitive_gate_and_switch_types       | x          | x      |
| instantiations                    | module_instantiation                  | x          | x      |
| instantiations                    | interface_instantiation               | x          | x      |
| instantiations                    | program_instantiation                 | x          | x      |
| instantiations                    | checker_instantiation                 | x          | x      |
| instantiations                    | generated_instantiation               | x          | x      |
| udp_declaration_and_instantiation | udp_declaration                       | x          | x      |
| udp_declaration_and_instantiation | udp_ports                             | x          | x      |
| udp_declaration_and_instantiation | udp_body                              | x          | x      |
| udp_declaration_and_instantiation | udp_instantiation                     | x          | x      |
| behavioral_statements             | continuous_assignment_and_net_alias   | x          | x      |
| behavioral_statements             | procedural_blocks_and_assignments     | x          | x      |
| behavioral_statements             | parallel_and_sequential_blocks        | x          | x      |
| behavioral_statements             | statements                            | x          | x      |
| behavioral_statements             | timing_control_statements             | x          | x      |
| behavioral_statements             | conditional_statements                | x          | x      |
| behavioral_statements             | case_statements                       | x          | x      |
| behavioral_statements             | patterns                              | x          | x      |
| behavioral_statements             | looping_statements                    | x          | x      |
| behavioral_statements             | subroutine_call_statements            | x          | x      |
| behavioral_statements             | assertion_statements                  | x          | x      |
| behavioral_statements             | clocking_block                        | x          | x      |
| behavioral_statements             | randsequence                          | x          | x      |
| specify_section                   | specify_block_declaration             | x          | x      |
| specify_section                   | specify_path_declarations             | x          | x      |
| specify_section                   | specify_block_terminals               | x          | x      |
| specify_section                   | specify_path_delays                   | x          | x      |
| specify_section                   | system_timing_check_commands          | x          | x      |
| specify_section                   | system_timing_check_command_arguments | x          | x      |
| specify_section                   | system_timing_check_event_definitions | x          | x      |
| expressions                       | concatenations                        | x          | x      |
| expressions                       | subroutine_calls                      | x          | x      |
| expressions                       | expressions                           | x          | x      |
| expressions                       | primaries                             | x          | x      |
| expressions                       | expression_leftside_values            | x          | x      |
| expressions                       | operators                             | x          | x      |
| expressions                       | numbers                               | x          | x      |
| expressions                       | strings                               | x          | x      |
| general                           | attributes                            | x          | x      |
| general                           | comments                              | x          | x      |
| general                           | identifiers                           | x          | x      |

# Test Status

| Clause | Exist | Pass | Clause | Exist | Pass | Clause | Exist | Pass | Clause | Exist | Pass |
| ------ | ----- | ---- | ------ | ----- | ---- | ------ | ----- | ---- | ------ | ----- | ---- |
| 3      | x     | x    | 13     | x     |      | 23     |       |      | 33     |       |      |
| 4      | x     | x    | 14     | x     |      | 24     |       |      | 34     |       |      |
| 5      | x     | x    | 15     | x     |      | 25     |       |      | 35     |       |      |
| 6      | x     |      | 16     | x     |      | 26     |       |      | 36     |       |      |
| 7      | x     |      | 17     |       |      | 27     |       |      | 37     |       |      |
| 8      | x     |      | 18     |       |      | 28     |       |      | 38     |       |      |
| 9      | x     |      | 19     |       |      | 29     |       |      | 39     |       |      |
| 10     | x     |      | 20     |       |      | 30     |       |      | 40     |       |      |
| 11     | x     |      | 21     |       |      | 31     |       |      |        |       |      |
| 12     | x     |      | 22     |       |      | 32     |       |      |        |       |      |

## Missing entry of specification

* interface_class_declaration -> connect to description/package_or_generate_item_declaration/anonymous_program_item
* formal_identifier -> ignore
* covergroup_variable_identifier -> ignore
* array_identifier -> ignore
