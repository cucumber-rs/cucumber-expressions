`cucumber-expressions` changelog
================================

All user visible changes to `cucumber-expressions` crate will be documented in this file. This project uses [Semantic Versioning 2.0.0].




## main

[Diff](https://github.com/cucumber-rs/cucumber-expressions/compare/v0.4.0...main)

### BC Breaks

- Bumped up [MSRV] to 1.85 because of migration to 2024 edition. ([todo])

[todo]: https://github.com/cucumber-rs/cucumber-expressions/commit/todo




## [0.4.0] · 2025-02-03
[0.4.0]: https://github.com/cucumber-rs/cucumber-expressions/tree/v0.4.0

[Diff](https://github.com/cucumber-rs/cucumber-expressions/compare/v0.3.0...v0.4.0)

### BC Breaks

- Bumped up [MSRV] to 1.81 because for `#[expect]` attribute usage. ([e1bb9266])
- Upgraded [`nom`] to 8.0 version and [`nom_locate`] to 5.0 version. ([#14], [356024ed])

### Updated

- [`derive_more`] to 2.0 version. ([#13])

[#13]: https://github.com/cucumber-rs/cucumber-expressions/pull/13
[#14]: https://github.com/cucumber-rs/cucumber-expressions/pull/14
[356024ed]: https://github.com/cucumber-rs/cucumber-expressions/commit/356024eddd10e3bcaa16c7b453a88ce2deb9cfc8
[e1bb9266]: https://github.com/cucumber-rs/cucumber-expressions/commit/e1bb92668617432948ab0faa32232b67d6c530e7




## [0.3.0] · 2023-04-24
[0.3.0]: https://github.com/cucumber-rs/cucumber-expressions/tree/v0.3.0

[Diff](https://github.com/cucumber-rs/cucumber-expressions/compare/v0.2.1...v0.3.0)

### BC Breaks

- Bumped up [MSRV] to 1.62 for more clever support of [Cargo feature]s.
- `Box`ed `ParameterError::RenameRegexGroup::err` field due to `clippy::result_large_err` lint suggestion.
- Upgraded [`regex-syntax`] to 0.7 version (changed parametrization of [`Regex`] with custom capturing groups). ([cd28fecc])

[cd28fecc]: https://github.com/cucumber-rs/cucumber-expressions/commit/cd28fecc62f5ee1942601053e5290968efa8244b




## [0.2.1] · 2022-03-09
[0.2.1]: https://github.com/cucumber-rs/cucumber-expressions/tree/v0.2.1

[Diff](https://github.com/cucumber-rs/cucumber-expressions/compare/v0.2.0...v0.2.1)

### Security updated

- [`regex`] crate to 1.5.5 version to fix [CVE-2022-24713].

[CVE-2022-24713]: https://blog.rust-lang.org/2022/03/08/cve-2022-24713.html




## [0.2.0] · 2022-02-10
[0.2.0]: https://github.com/cucumber-rs/cucumber-expressions/tree/v0.2.0

[Diff](https://github.com/cucumber-rs/cucumber-expressions/compare/v0.1.2...v0.2.0) | [Milestone](https://github.com/cucumber-rs/cucumber-expressions/milestone/4)

### BC Breaks

- Added `id` field to `Parameter` AST struct. ([#8], [#7])

### Added

- Support of capturing groups inside `Parameter` regex. ([#8], [#7])

[#7]: https://github.com/cucumber-rs/cucumber-expressions/issues/7
[#8]: https://github.com/cucumber-rs/cucumber-expressions/pull/8




## [0.1.2] · 2022-01-11
[0.1.2]: https://github.com/cucumber-rs/cucumber-expressions/tree/v0.1.2

[Diff](https://github.com/cucumber-rs/cucumber-expressions/compare/v0.1.1...v0.1.2) | [Milestone](https://github.com/cucumber-rs/cucumber-expressions/milestone/3)

### Fixed

- Unsupported lookaheads in `float` parameter's [`Regex`]. ([#6], [cucumber-rs/cucumber#197])

[#6]: https://github.com/cucumber-rs/cucumber-expressions/pull/6
[cucumber-rs/cucumber#197]: https://github.com/cucumber-rs/cucumber/issues/197




## [0.1.1] · 2021-11-29
[0.1.1]: https://github.com/cucumber-rs/cucumber-expressions/tree/v0.1.1

[Diff](https://github.com/cucumber-rs/cucumber-expressions/compare/v0.1.0...v0.1.1) | [Milestone](https://github.com/cucumber-rs/cucumber-expressions/milestone/2)

### Updated

- [`derive_more`] minimal version to `0.99.17`. ([#5])

[#5]: https://github.com/cucumber-rs/cucumber-expressions/pull/5




## [0.1.0] · 2021-11-22
[0.1.0]: https://github.com/cucumber-rs/cucumber-expressions/tree/v0.1.0

[Milestone](https://github.com/cucumber-rs/cucumber-expressions/milestone/1)

### Added

- [Cucumber Expressions] AST and parser. ([#1])
- Expansion of [Cucumber Expressions] AST into [`Regex`] behind `into-regex` feature flag. ([#2])
- Fuzzing. ([#3])

[#1]: https://github.com/cucumber-rs/cucumber-expressions/pull/1
[#2]: https://github.com/cucumber-rs/cucumber-expressions/pull/2
[#3]: https://github.com/cucumber-rs/cucumber-expressions/pull/3




[`derive_more`]: https://docs.rs/derive_more
[`nom`]: https://docs.rs/nom
[`nom_locate`]: https://docs.rs/nom_locate
[`regex`]: https://docs.rs/regex
[`Regex`]: https://docs.rs/regex
[`regex-syntax`]: https://docs.rs/regex-syntax

[Cargo feature]: https://doc.rust-lang.org/cargo/reference/features.html
[Cucumber Expressions]: https://github.com/cucumber/cucumber-expressions#readme
[MSRV]: https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field
[Semantic Versioning 2.0.0]: https://semver.org
