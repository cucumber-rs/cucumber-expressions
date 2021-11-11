[Cucumber Expressions] for Rust
===============================

[![Documentation](https://docs.rs/cucumber-expressions/badge.svg)](https://docs.rs/cucumber-expressions)
[![CI](https://github.com/cucumber-rs/cucumber-expressions/workflows/CI/badge.svg?branch=master "CI")](https://github.com/cucumber-rs/cucumber-expressions/actions?query=workflow%3ACI+branch%3Amaster)
[![Rust 1.56+](https://img.shields.io/badge/rustc-1.56+-lightgray.svg "Rust 1.56+")](https://blog.rust-lang.org/2021/10/21/Rust-1.56.0.html)
[![Unsafe Forbidden](https://img.shields.io/badge/unsafe-forbidden-success.svg)](https://github.com/rust-secure-code/safety-dance)

- [Changelog](https://github.com/cucumber-rs/cucumber-expressions/blob/main/CHANGELOG.md)

Rust implementation of [Cucumber Expressions].

This crate provides [AST] parser, and [Regex] expansion of [Cucumber Expressions].

```rust
use cucumber_expressions::Expression;

let re = Expression::regex("I have {int} cucumbers in my belly").unwrap();
let caps = re.captures("I have 42 cucumbers in my belly").unwrap();

assert_eq!(&caps[0], "I have 42 cucumbers in my belly");
assert_eq!(&caps[1], "42");
```




## License

This project is licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](https://github.com/cucumber-rs/cucumber-expressions/blob/main/LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT](https://github.com/cucumber-rs/cucumber-expressions/blob/main/LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.




[AST]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
[Cucumber Expressions]: https://github.com/cucumber/cucumber-expressions#readme
[Regex]: https://docs.rs/regex/
