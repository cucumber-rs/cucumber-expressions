[Cucumber Expressions] for Rust
===============================

[![Documentation](https://docs.rs/cucumber-expressions/badge.svg)](https://docs.rs/cucumber-expressions)
[![CI](https://github.com/cucumber-rs/cucumber-expressions/workflows/CI/badge.svg?branch=master "CI")](https://github.com/cucumber-rs/cucumber-expressions/actions?query=workflow%3ACI+branch%3Amaster)
[![Rust 1.56+](https://img.shields.io/badge/rustc-1.56+-lightgray.svg "Rust 1.56+")](https://blog.rust-lang.org/2021/10/21/Rust-1.56.0.html)
[![Unsafe Forbidden](https://img.shields.io/badge/unsafe-forbidden-success.svg)](https://github.com/rust-secure-code/safety-dance)

- [Changelog](https://github.com/cucumber-rs/cucumber-expressions/blob/main/CHANGELOG.md)

Rust implementation of [Cucumber Expressions].

This crate provides [AST] and parser of [Cucumber Expressions].




## Grammar

This implementation follows context-free grammar, [which isn't yet merged][1]. Original grammar is impossible to follow while creating performant parser, as it consists errors and describes not `Cucumber Expressions`, but some superset language and context-sensitive. In case you've found some inconsistencies between implementations in other languages, please file an issue! 

[EBNF] spec
```ebnf
expression              = single-expression*

single-expression       = alternation
                           | optional
                           | parameter
                           | text-without-whitespace+
                           | whitespace
text-without-whitespace = (- (text-to-escape | whitespace))
                           | ('\', text-to-escape)
text-to-escape          = '(' | '{' | '/' | '\'

alternation             = single-alternation, (`/`, single-alternation)+
single-alternation      = ((text-in-alternative+, optional*)
                            | (optional+, text-in-alternative+))+
text-in-alternative     = (- alternative-to-escape)
                           | ('\', alternative-to-escape)
alternative-to-escape   = ' ' | '(' | '{' | '/' | '\'

optional                = '(' text-in-optional+ ')'
text-in-optional        = (- optional-to-escape) | ('\', optional-to-escape)
optional-to-escape      = '(' | ')' | '{' | '/' | '\'

parameter               = '{', name*, '}'
name                    = (- name-to-escape) | ('\', name-to-escape)
name-to-escape          = '{' | '}' | '(' | '/' | '\'
```




## License

This project is licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](https://github.com/cucumber-rs/cucumber-expressions/blob/main/LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT](https://github.com/cucumber-rs/cucumber-expressions/blob/main/LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.




[1]: https://github.com/cucumber/cucumber-expressions/issues/41
[AST]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
[Cucumber Expressions]: https://github.com/cucumber/cucumber-expressions#readme
[EBNF]: https://en.wikipedia.org/wiki/Extended_Backus–Naur_form
