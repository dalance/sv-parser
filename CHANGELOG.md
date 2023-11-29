# Change Log

## [Unreleased](https://github.com/dalance/sv-parser/compare/v0.13.2...Unreleased) - ReleaseDate

* [Fixed] Fix chained method [#93](https://github.com/dalance/sv-parser/pull/93)

## [v0.13.2](https://github.com/dalance/sv-parser/compare/v0.13.1...v0.13.2) - 2023-11-09

* [Changed] Modify to handle symplink as well as file [#87](https://github.com/dalance/sv-parser/pull/87)

## [v0.13.1](https://github.com/dalance/sv-parser/compare/v0.13.0...v0.13.1) - 2023-03-23

* [Changed] update nom to 7

## [v0.13.0](https://github.com/dalance/sv-parser/compare/v0.12.3...v0.13.0) - 2023-02-08

* [Added] Improvement: Handle non-UTF8 files [#79](https://github.com/dalance/sv-parser/pull/79)

## [v0.12.2](https://github.com/dalance/sv-parser/compare/v0.12.1...v0.12.2) - 2022-11-09

* [Fixed] fix: typo [#65](https://github.com/dalance/sv-parser/pull/65)
* [Added] Implement the std::fmt::Debug trait. [#70](https://github.com/dalance/sv-parser/pull/70)
* [Changed] Predefine SV_COV_* constants required by clause 40.3.1 [#71](https://github.com/dalance/sv-parser/pull/71)
* [Changed] Use Error::Preprocess on pp parsing error, instead of Error::Parse. [#69](https://github.com/dalance/sv-parser/pull/69)

## [v0.12.1](https://github.com/dalance/sv-parser/compare/v0.12.0...v0.12.1) - 2022-08-01

* [Fixed] Bugfixes for preprocess(), plus organise and extend tests. [#61](https://github.com/dalance/sv-parser/pull/61)

## [v0.12.0](https://github.com/dalance/sv-parser/compare/v0.11.3...v0.12.0) - 2022-07-05

* [Fixed] Fix issues #49 and #50 [#51](https://github.com/dalance/sv-parser/pull/51)
* [Fixed] Remove whitespace within/around compiler directives (bugfix). [#58](https://github.com/dalance/sv-parser/pull/58)

## [v0.11.3](https://github.com/dalance/sv-parser/compare/v0.11.2...v0.11.3) - 2022-02-03

## [v0.11.2](https://github.com/dalance/sv-parser/compare/v0.11.1...v0.11.2) - 2021-11-12

* [Changed] pub access to Define members

## [v0.11.1](https://github.com/dalance/sv-parser/compare/v0.11.0...v0.11.1) - 2021-03-05

* [Fixed] include with comment error

## [v0.11.0](https://github.com/dalance/sv-parser/compare/v0.10.8...v0.11.0) - 2021-03-04

* [Changed] keep directives after preprocess

## [v0.10.8](https://github.com/dalance/sv-parser/compare/v0.10.7...v0.10.8) - 2021-01-29

* [Fixed] include with comment error

## [v0.10.7](https://github.com/dalance/sv-parser/compare/v0.10.6...v0.10.7) - 2021-01-29

* [Added] get_str_trim to SyntaxTree

## [v0.10.6](https://github.com/dalance/sv-parser/compare/v0.10.5...v0.10.6) - 2021-01-28

* [Fixed] constant_expression_ternary priority [#30](https://github.com/dalance/sv-parser/issues/30)

## [v0.10.5](https://github.com/dalance/sv-parser/compare/v0.10.4...v0.10.5) - 2021-01-19

* [Fixed] missing comment after macro name [#29](https://github.com/dalance/sv-parser/issues/29)

## [v0.10.4](https://github.com/dalance/sv-parser/compare/v0.10.3...v0.10.4) - 2021-01-08

* [Fixed] uncleared internal state

## [v0.10.3](https://github.com/dalance/sv-parser/compare/v0.10.2...v0.10.3) - 2021-01-08

* [Fixed] empty port list is parsed as non-ANSI style

## [v0.10.2](https://github.com/dalance/sv-parser/compare/v0.10.1...v0.10.2) - 2021-01-06

* [Fixed] embedded single line comment in macro [#28](https://github.com/dalance/sv-parser/issues/28)

## [v0.10.1](https://github.com/dalance/sv-parser/compare/v0.10.0...v0.10.1) - 2021-01-05

* [Fixed] Use many_till instead of many0 for accurate error position

## [v0.10.0](https://github.com/dalance/sv-parser/compare/v0.9.0...v0.10.0) - 2020-12-24

* [Fixed] wrong error position
* [Fixed] escaped_ideitifier at macro name [#28](https://github.com/dalance/sv-parser/issues/28)
* [Fixed] begin_keywords "1364-2001-noconfig" failure [#28](https://github.com/dalance/sv-parser/issues/28)
* [Changed] update nom to 6.0.0

## [v0.9.0](https://github.com/dalance/sv-parser/compare/v0.8.3...v0.9.0) - 2020-11-11

* [Added] define option to parse_sv
* [Added] incomplete option [#19](https://github.com/dalance/sv-parser/issues/19)
* [Changed] keep text_macro_definition after preprocess [#19](https://github.com/dalance/sv-parser/issues/19)

## [v0.8.3](https://github.com/dalance/sv-parser/compare/v0.8.2...v0.8.3) - 2020-11-06

* [Fixed] textmacro without arguments issue [#20](https://github.com/dalance/sv-parser/issues/20)

## [v0.8.2](https://github.com/dalance/sv-parser/compare/v0.8.1...v0.8.2) - 2020-08-28

* [Fixed] empty ifdef issue [#10](https://github.com/dalance/sv-parser/issues/10)

## [v0.8.1](https://github.com/dalance/sv-parser/compare/v0.8.0...v0.8.1) - 2020-08-28

* [Fixed] text macro with single line comment [#12](https://github.com/dalance/sv-parser/issues/12)

## [v0.8.0](https://github.com/dalance/sv-parser/compare/v0.7.0...v0.8.0) - 2020-08-28

* [Fixed] 'Declaraton' typo [#18](https://github.com/dalance/sv-parser/issues/18)

## [v0.7.0](https://github.com/dalance/sv-parser/compare/v0.6.5...v0.7.0) - 2020-04-10

* [Changed] make comment stripping optional [#6](https://github.com/dalance/sv-parser/pull/6)

## [v0.6.5](https://github.com/dalance/sv-parser/compare/v0.6.4...v0.6.5) - 2020-04-03

* [Fixed] casting parse error [#8](https://github.com/dalance/sv-parser/issues/8)
* [Changed] update nom_locate to 2.0.0

## [v0.6.4](https://github.com/dalance/sv-parser/compare/v0.6.3...v0.6.4) - 2020-03-12

* [Changed] error message of Error::Io

## [v0.6.3](https://github.com/dalance/sv-parser/compare/v0.6.2...v0.6.3) - 2020-02-13

## [v0.6.2](https://github.com/dalance/sv-parser/compare/v0.6.1...v0.6.2) - 2020-02-13

* [Fixed] parse error of cast

## [v0.6.1](https://github.com/dalance/sv-parser/compare/v0.6.0...v0.6.1) - 2020-02-09

* [Changed] update str-concat

## [v0.6.0](https://github.com/dalance/sv-parser/compare/v0.5.0...v0.6.0) - 2020-01-24

* [Added] ignore_include option

## [v0.5.0](https://github.com/dalance/sv-parser/compare/v0.4.20...v0.5.0) - 2020-01-23

* [Changed] from `sv-parser-error::ErrorKind` to `sv-parser-error::Error`
* [Changed] Refine parse_sv -t option
* [Added] Display trait of SyntaxTree

## [v0.4.20](https://github.com/dalance/sv-parser/compare/v0.4.19...v0.4.20) - 2020-01-22

* [Fixed] macro arguments spacing
* [Added] `` `__LINE__`` and `` `__FILE__`` are preprocessed
* [Fixed] parser priority about specify
* [Fixed] escaped_ideitifier including `` ` ``
* [Fixed] time_literal spacing

## [v0.4.19](https://github.com/dalance/sv-parser/compare/v0.4.18...v0.4.19) - 2019-12-12

* [Added] include line check
* [Fixed] resetall directive in design element

## [v0.4.18](https://github.com/dalance/sv-parser/compare/v0.4.17...v0.4.18) - 2019-12-12

## [v0.4.17](https://github.com/dalance/sv-parser/compare/v0.4.16...v0.4.17) - 2019-12-12

## [v0.4.16](https://github.com/dalance/sv-parser/compare/v0.4.15...v0.4.16) - 2019-12-12

## [v0.4.15](https://github.com/dalance/sv-parser/compare/v0.4.14...v0.4.15) - 2019-12-12

## [v0.4.14](https://github.com/dalance/sv-parser/compare/v0.4.13...v0.4.14) - 2019-12-12

## [v0.4.13](https://github.com/dalance/sv-parser/compare/v0.4.12...v0.4.13) - 2019-12-12

## [v0.4.12](https://github.com/dalance/sv-parser/compare/v0.4.11...v0.4.12) - 2019-12-12

## [v0.4.11](https://github.com/dalance/sv-parser/compare/v0.4.10...v0.4.11) - 2019-12-12

## [v0.4.10](https://github.com/dalance/sv-parser/compare/v0.4.9...v0.4.10) - 2019-12-12

## [v0.4.9](https://github.com/dalance/sv-parser/compare/v0.4.8...v0.4.9) - 2019-12-12

## [v0.4.8](https://github.com/dalance/sv-parser/compare/v0.4.7...v0.4.8) - 2019-12-12

* [Fixed] allow recursive define until limit

## [v0.4.7](https://github.com/dalance/sv-parser/compare/v0.4.6...v0.4.7) - 2019-12-10

* [Added] recursive define detection

## [v0.4.6](https://github.com/dalance/sv-parser/compare/v0.4.5...v0.4.6) - 2019-12-02

* [Fixed] constant_bit_select
* [Fixed] wrong linebreak at define macro usage

## [v0.4.5](https://github.com/dalance/sv-parser/compare/v0.4.4...v0.4.5) - 2019-11-28

* [Fixed] wrong space at define macro usage

## [v0.4.4](https://github.com/dalance/sv-parser/compare/v0.4.3...v0.4.4) - 2019-11-22

* [Fixed] \`resetall wrongly clear define list

## [v0.4.3](https://github.com/dalance/sv-parser/compare/v0.4.2...v0.4.3) - 2019-11-15

* [Added] parse_sv_str/parse_lib_str

## [v0.4.2](https://github.com/dalance/sv-parser/compare/v0.4.1...v0.4.2) - 2019-11-12

* [Added] re-export DefineText

## [v0.4.1](https://github.com/dalance/sv-parser/compare/v0.4.0...v0.4.1) - 2019-11-12

## [v0.4.0](https://github.com/dalance/sv-parser/compare/v0.3.7...v0.4.0) - 2019-11-12

* [Changed] origin of define to optional

## [v0.3.7](https://github.com/dalance/sv-parser/compare/v0.3.6...v0.3.7) - 2019-11-06

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
