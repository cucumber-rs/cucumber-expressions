[Cucumber Expressions] for Rust
===============================

[![crates.io](https://img.shields.io/crates/v/cucumber-expressions.svg?maxAge=2592000 "crates.io")](https://crates.io/crates/cucumber-expressions)
[![Rust 1.62+](https://img.shields.io/badge/rustc-1.62+-lightgray.svg "Rust 1.62+")](https://blog.rust-lang.org/2022/06/30/Rust-1.62.0.html)
[![Unsafe Forbidden](https://img.shields.io/badge/unsafe-forbidden-success.svg "Unsafe forbidden")](https://github.com/rust-secure-code/safety-dance)  
[![CI](https://github.com/cucumber-rs/cucumber-expressions/workflows/CI/badge.svg?branch=main "CI")](https://github.com/cucumber-rs/cucumber-expressions/actions?query=workflow%3ACI+branch%3Amaster)
[![Rust docs](https://docs.rs/cucumber-expressions/badge.svg "Rust docs")](https://docs.rs/cucumber-expressions)

- [Changelog](https://github.com/cucumber-rs/cucumber-expressions/blob/main/CHANGELOG.md)

Rust implementation of [Cucumber Expressions].

This crate provides [AST] parser, and [`Regex`] expansion of [Cucumber Expressions].

```rust
# // `Regex` expansion requires `into-regex` feature.
# #[cfg(feature = "into-regex")] {
use cucumber_expressions::Expression;

let re = Expression::regex("I have {int} cucumbers in my belly").unwrap();
let caps = re.captures("I have 42 cucumbers in my belly").unwrap();

assert_eq!(&caps[0], "I have 42 cucumbers in my belly");
assert_eq!(&caps[1], "42");
# }
```




## Cargo features

- `into-regex`: Enables expansion into [`Regex`].




## Grammar

This implementation follows a context-free grammar, [which isn't yet merged][1]. Original grammar is impossible to follow while creating a performant parser, as it consists errors and describes not an exact [Cucumber Expressions] language, but rather some superset language, while being also context-sensitive. In case you've found some inconsistencies between this implementation and the ones in other languages, please file an issue! 

[EBNF] spec of the current context-free grammar implemented by this crate:
```ebnf
expression              = single-expression*

single-expression       = alternation
                           | optional
                           | parameter
                           | text-without-whitespace+
                           | whitespace+
text-without-whitespace = (- (text-to-escape | whitespace))
                           | ('\', text-to-escape)
text-to-escape          = '(' | '{' | '/' | '\'

alternation             = single-alternation, (`/`, single-alternation)+
single-alternation      = ((text-in-alternative+, optional*)
                            | (optional+, text-in-alternative+))+
text-in-alternative     = (- alternative-to-escape)
                           | ('\', alternative-to-escape)
alternative-to-escape   = whitespace | '(' | '{' | '/' | '\'
whitespace              = ' '

optional                = '(' text-in-optional+ ')'
text-in-optional        = (- optional-to-escape) | ('\', optional-to-escape)
optional-to-escape      = '(' | ')' | '{' | '/' | '\'

parameter               = '{', name*, '}'
name                    = (- name-to-escape) | ('\', name-to-escape)
name-to-escape          = '{' | '}' | '(' | '/' | '\'
```




## [`Regex`] Production Rules

Follows original [production rules][2].




## License

This project is licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](https://github.com/cucumber-rs/cucumber-expressions/blob/main/LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT](https://github.com/cucumber-rs/cucumber-expressions/blob/main/LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.




[`Regex`]: https://docs.rs/regex

[AST]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
[Cucumber Expressions]: https://github.com/cucumber/cucumber-expressions#readme
[EBNF]: https://en.wikipedia.org/wiki/Extended_Backus–Naur_form

[1]: https://github.com/cucumber/cucumber-expressions/issues/41
[2]: https://github.com/cucumber/cucumber-expressions/blob/main/ARCHITECTURE.md#production-rules
