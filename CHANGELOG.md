# Change Log

## [Unreleased](https://github.com/dalance/sv-parser/compare/v0.2.1...Unreleased) - ReleaseDate

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
