# Change Log

## [Unreleased](https://github.com/dalance/sv-parser/compare/v0.3.6...Unreleased) - ReleaseDate

* [Fixed] apply workaround for static class method call
* [Fixed] randomize_call bug
* [Fixed] parameter override by class type bug
* [Fixed] hierarchical this bug
* [Fixed] hierarchical delay value bug
* [Fixed] const class new bug
* [Fixed] missing all_consuming of pp_parser
* [Fixed] typo 'triwand'
* [Fixed] arguments of text_macro_usage

## [v0.3.6](https://github.com/dalance/sv-parser/compare/v0.3.5...v0.3.6) - 2019-11-05

## [v0.3.5](https://github.com/dalance/sv-parser/compare/v0.3.4...v0.3.5) - 2019-11-05

* [Added] LF/CR+LF support
* [Added] empty define support

## [v0.3.4](https://github.com/dalance/sv-parser/compare/v0.3.3...v0.3.4) - 2019-11-05

* [Fixed] define with string literal

## [v0.3.3](https://github.com/dalance/sv-parser/compare/v0.3.2...v0.3.3) - 2019-11-01

* [Fixed] define arument
* [Fixed] text macro identifier

## [v0.3.2](https://github.com/dalance/sv-parser/compare/v0.2.1...v0.3.2) - 2019-10-29

* [Changed] SyntaxTree::get_str can take &RefNode
* [Added] unwrap_locate macro
* [Fixed] iterator order

## [v0.2.1](https://github.com/dalance/sv-parser/compare/v0.2.0...v0.2.1) - 2019-10-28

* [Added] get_origin to SyntaxTree
* [Added] re-export Error/ErrorKind
* [Fixed] unwrap_node import
* [Fixed] spacing of text macro usage

## [v0.2.0](https://github.com/dalance/sv-parser/compare/v0.1.4...v0.2.0) - 2019-10-16

* [Added] parse error position
* [Fixed] spacing rule aroung text_macro_identifier
* [Fixed] cond_predicate in cond_predicate
* [Fixed] fixed_number priority in delay_value
* [Fixed] cast/const_cast priority
* [Added] unwrap_node macro
