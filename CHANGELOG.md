`cucumber-expressions` changelog
================================

All user visible changes to `cucumber-expressions` crate will be documented in this file. This project uses [Semantic Versioning 2.0.0].




## [0.1.2] · 2022-01-11
[0.1.2]: /../../tree/v0.1.2

[Diff](/../../compare/v0.1.1...v0.1.2) | [Milestone](/../../milestone/3)

### Fixed

- Unsupported lookaheads in `float` parameter's [`Regex`]. ([#6], [cucumber-rs/cucumber#197])

[#6]: /../../pull/6
[cucumber-rs/cucumber#197]: https://github.com/cucumber-rs/cucumber/issues/197




## [0.1.1] · 2021-11-29
[0.1.1]: /../../tree/v0.1.1

[Diff](/../../compare/v0.1.0...v0.1.1) | [Milestone](/../../milestone/2)

### Updated

- [`derive_more`] minimal version to `0.99.17`. ([#5])

[#5]: /../../pull/5
[`derive_more`]: https://docs.rs/derive_more




## [0.1.0] · 2021-11-22
[0.1.0]: /../../tree/v0.1.0

[Milestone](/../../milestone/1)

### Added

- [Cucumber Expressions] AST and parser. ([#1])
- Expansion of [Cucumber Expressions] AST into [`Regex`] behind `into-regex` feature flag. ([#2])
- Fuzzing. ([#3])

[#1]: /../../pull/1
[#2]: /../../pull/2
[#3]: /../../pull/3




[`Regex`]: https://docs.rs/regex

[Cucumber Expressions]: https://github.com/cucumber/cucumber-expressions#readme
[Semantic Versioning 2.0.0]: https://semver.org
