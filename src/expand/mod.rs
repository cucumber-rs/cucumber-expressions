// Copyright (c) 2021  Brendan Molloy <brendan@bbqsrc.net>,
//                     Ilya Solovyiov <ilya.solovyiov@gmail.com>,
//                     Kai Ren <tyranron@gmail.com>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! [Cucumber Expressions][1] [AST][2] into [`Regex`] transformation
//! definitions.
//!
//! [1]: https://github.com/cucumber/cucumber-expressions#readme
//! [2]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
//! [`Regex`]: regex::Regex

pub mod with_parameters;

use std::{fmt, iter, str, vec};

use derive_more::{Display, Error, From};
use either::Either;
use nom::{AsChar, InputIter};
use regex::Regex;

use crate::{
    parse, Alternation, Alternative, Expression, Optional, Parameter,
    SingleAlternation, SingleExpression, Spanned,
};

pub use with_parameters::{ParametersProvider, WithParameters};

impl<'s> Expression<Spanned<'s>> {
    /// Transforms `Input` into [`Regex`].
    ///
    /// # Parameter types
    ///
    /// Text between curly braces reference a *parameter type*. Cucumber
    /// comes with the following built-in parameter types:
    ///
    /// | Parameter Type  | Description |
    /// | --------------- | ----------- |
    /// | `{int}`         | Matches integers |
    /// | `{float}`       | Matches floats |
    /// | `{word}`        | Matches words without whitespace |
    /// | `{string}`      | Matches single-quoted or double-quoted strings |
    /// | `{}` anonymous  | Matches anything (`/.*/`) |
    ///
    /// # Errors
    ///
    /// See [`Error`] for more details.
    ///
    /// [`Error`]: ExpansionError
    pub fn regex<Input: AsRef<str> + ?Sized>(
        input: &'s Input,
    ) -> Result<Regex, ExpansionError<Spanned<'s>>> {
        let re_str = Expression::parse(input)?
            .into_regex_char_iter()
            .collect::<Result<String, _>>()?;
        Regex::new(&re_str).map_err(Into::into)
    }

    /// Transforms `Input` into [`Regex`] with `Parameters` in addition to
    /// the [default ones][1]
    ///
    /// # Errors
    ///
    /// See [`Error`] for more details.
    ///
    /// [1]: Expression#parameter-types
    /// [`Error`]: ExpansionError
    pub fn regex_with_parameters<Input, Parameters>(
        input: &'s Input,
        parameters: Parameters,
    ) -> Result<Regex, ExpansionError<Spanned<'s>>>
    where
        Input: AsRef<str> + ?Sized,
        Parameters: Clone + ParametersProvider<Spanned<'s>>,
        Parameters::Value: InputIter,
        <Parameters::Value as InputIter>::Item: AsChar,
    {
        let re_str = Expression::parse(input)?
            .with_parameters(parameters)
            .into_regex_char_iter()
            .collect::<Result<String, _>>()?;
        Regex::new(&re_str).map_err(Into::into)
    }

    /// Adds [`ParametersProvider`] for transforming into [`Regex`].
    pub fn with_parameters<P: ParametersProvider<Spanned<'s>>>(
        self,
        parameters: P,
    ) -> WithParameters<Self, P> {
        WithParameters {
            item: self,
            parameters,
        }
    }
}

/// Possible errors while transforming `Input` representing
/// [Cucumber Expression][1] into [`Regex`]
///
/// [1]: https://github.com/cucumber/cucumber-expressions#readme
#[derive(Clone, Debug, Display, Error, From)]
pub enum ExpansionError<Input>
where
    Input: fmt::Display,
{
    /// Parsing error.
    #[display(fmt = "Parsing failed: {}", _0)]
    Parsing(parse::Error<Input>),

    /// Expansion error.
    #[display(fmt = "Regex expansion failed: {}", _0)]
    Expansion(UnknownParameterError<Input>),

    /// Regex error.
    #[display(fmt = "Regex failed: {}", _0)]
    Regex(regex::Error),
}

/// [`Parameter`] not found.
#[derive(Clone, Copy, Debug, Display, Error)]
#[display(fmt = "Parameter '{}' not found.", not_found)]
pub struct UnknownParameterError<Input>
where
    Input: fmt::Display,
{
    /// [`Parameter`] not found.
    pub not_found: Input,
}

/// Trait for converting [Cucumber Expressions][1] [AST][2] elements into
/// [`Iterator`]'<'[`Item`]` = `[`char`]`>` for transforming into [`Regex`].
///
/// [1]: https://github.com/cucumber/cucumber-expressions#readme
/// [2]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
/// [`Item`]: Iterator::Item
pub trait IntoRegexCharIter<Input: fmt::Display> {
    /// [`Iterator`] for transforming into [`Regex`].
    type Iter: Iterator<Item = Result<char, UnknownParameterError<Input>>>;

    /// Returns [`Iterator`] for transforming into [`Regex`].
    fn into_regex_char_iter(self) -> Self::Iter;
}

impl<Input> IntoRegexCharIter<Input> for Expression<Input>
where
    Input: Clone + fmt::Display + InputIter,
    <Input as InputIter>::Item: AsChar,
{
    type Iter = ExpressionIter<Input>;

    fn into_regex_char_iter(self) -> Self::Iter {
        let into_regex_char_iter: fn(_) -> _ =
            IntoRegexCharIter::into_regex_char_iter;
        iter::once(Ok('^'))
            .chain(self.0.into_iter().flat_map(into_regex_char_iter))
            .chain(iter::once(Ok('$')))
    }
}

/// [`IntoRegexCharIter::Iter`] for [`Expression`].
type ExpressionIter<Input> = iter::Chain<
    iter::Chain<
        iter::Once<Result<char, UnknownParameterError<Input>>>,
        iter::FlatMap<
            vec::IntoIter<SingleExpression<Input>>,
            <SingleExpression<Input> as IntoRegexCharIter<Input>>::Iter,
            fn(
                SingleExpression<Input>,
            )
                -> <SingleExpression<Input> as IntoRegexCharIter<Input>>::Iter,
        >,
    >,
    iter::Once<Result<char, UnknownParameterError<Input>>>,
>;

impl<Input> IntoRegexCharIter<Input> for SingleExpression<Input>
where
    Input: Clone + fmt::Display + InputIter,
    <Input as InputIter>::Item: AsChar,
{
    type Iter = SingleExpressionIter<Input>;

    fn into_regex_char_iter(self) -> Self::Iter {
        use Either::{Left, Right};

        let ok: fn(_) -> _ = Ok;
        let as_char: fn(_) -> _ = AsChar::as_char;

        match self {
            Self::Alternation(alt) => Left(alt.into_regex_char_iter()),
            Self::Optional(opt) => Right(Left(opt.into_regex_char_iter())),
            Self::Parameter(p) => Right(Right(Left(p.into_regex_char_iter()))),
            Self::Text(t) => Right(Right(Right(Left(
                EscapeForRegex::new(t.iter_elements().map(as_char)).map(ok),
            )))),
            Self::Whitespace => Right(Right(Right(Right(iter::once(Ok(' ')))))),
        }
    }
}

/// [`IntoRegexCharIter::Iter`] for [`SingleExpression`].
type SingleExpressionIter<Input> = Either<
    <Alternation<Input> as IntoRegexCharIter<Input>>::Iter,
    Either<
        <Optional<Input> as IntoRegexCharIter<Input>>::Iter,
        Either<
            <Parameter<Input> as IntoRegexCharIter<Input>>::Iter,
            Either<
                iter::Map<
                    EscapeForRegex<
                        iter::Map<
                            <Input as InputIter>::IterElem,
                            fn(<Input as InputIter>::Item) -> char,
                        >,
                    >,
                    MapOkChar<Input>,
                >,
                iter::Once<Result<char, UnknownParameterError<Input>>>,
            >,
        >,
    >,
>;

impl<Input> IntoRegexCharIter<Input> for Alternation<Input>
where
    Input: fmt::Display + InputIter,
    <Input as InputIter>::Item: AsChar,
{
    type Iter = AlternationIter<Input>;

    fn into_regex_char_iter(self) -> Self::Iter {
        let ok: fn(_) -> _ = Ok;
        let single_alt: fn(SingleAlternation<Input>) -> _ = |alt| {
            let into_regex_char_iter: fn(_) -> _ =
                IntoRegexCharIter::into_regex_char_iter;

            alt.into_iter()
                .flat_map(into_regex_char_iter)
                .chain(iter::once(Ok('|')))
        };

        "(?:"
            .chars()
            .map(ok)
            .chain(SkipLast::new(self.0.into_iter().flat_map(single_alt)))
            .chain(iter::once(Ok(')')))
    }
}

/// [`IntoRegexCharIter::Iter`] for [`Alternation`].
type AlternationIter<I> = iter::Chain<
    iter::Chain<
        iter::Map<str::Chars<'static>, MapOkChar<I>>,
        SkipLast<
            iter::FlatMap<
                vec::IntoIter<SingleAlternation<I>>,
                AlternationIterInner<I>,
                fn(SingleAlternation<I>) -> AlternationIterInner<I>,
            >,
        >,
    >,
    iter::Once<Result<char, UnknownParameterError<I>>>,
>;

/// Inner type for [`AlternationIter`].
type AlternationIterInner<I> = iter::Chain<
    iter::FlatMap<
        vec::IntoIter<Alternative<I>>,
        <Alternative<I> as IntoRegexCharIter<I>>::Iter,
        fn(Alternative<I>) -> <Alternative<I> as IntoRegexCharIter<I>>::Iter,
    >,
    iter::Once<Result<char, UnknownParameterError<I>>>,
>;

impl<Input> IntoRegexCharIter<Input> for Alternative<Input>
where
    Input: fmt::Display + InputIter,
    <Input as InputIter>::Item: AsChar,
{
    type Iter = AlternativeIter<Input>;

    fn into_regex_char_iter(self) -> Self::Iter {
        use Either::{Left, Right};

        let as_char: fn(<Input as InputIter>::Item) -> char = AsChar::as_char;
        match self {
            Self::Optional(opt) => Left(opt.into_regex_char_iter()),
            Self::Text(text) => Right(
                EscapeForRegex::new(text.iter_elements().map(as_char)).map(Ok),
            ),
        }
    }
}

/// [`IntoRegexCharIter::Iter`] for [`Alternative`].
type AlternativeIter<Input> = Either<
    <Optional<Input> as IntoRegexCharIter<Input>>::Iter,
    iter::Map<
        EscapeForRegex<
            iter::Map<
                <Input as InputIter>::IterElem,
                fn(<Input as InputIter>::Item) -> char,
            >,
        >,
        MapOkChar<Input>,
    >,
>;

impl<Input> IntoRegexCharIter<Input> for Optional<Input>
where
    Input: fmt::Display + InputIter,
    <Input as InputIter>::Item: AsChar,
{
    type Iter = OptionalIter<Input>;

    fn into_regex_char_iter(self) -> Self::Iter {
        let as_char: fn(<Input as InputIter>::Item) -> char = AsChar::as_char;
        "(?:"
            .chars()
            .chain(EscapeForRegex::new(self.0.iter_elements().map(as_char)))
            .chain(")?".chars())
            .map(Ok)
    }
}

/// [`IntoRegexCharIter::Iter`] for [`Optional`].
type OptionalIter<Input> = iter::Map<
    iter::Chain<
        iter::Chain<
            str::Chars<'static>,
            EscapeForRegex<
                iter::Map<
                    <Input as InputIter>::IterElem,
                    fn(<Input as InputIter>::Item) -> char,
                >,
            >,
        >,
        str::Chars<'static>,
    >,
    MapOkChar<Input>,
>;

/// Alias for [`Ok`].
type MapOkChar<Input> = fn(char) -> Result<char, UnknownParameterError<Input>>;

impl<Input> IntoRegexCharIter<Input> for Parameter<Input>
where
    Input: Clone + fmt::Display + InputIter,
    <Input as InputIter>::Item: AsChar,
{
    type Iter = ParameterIter<Input>;

    fn into_regex_char_iter(self) -> Self::Iter {
        use Either::{Left, Right};

        let eq = |i: &Input, str: &str| {
            i.iter_elements().map(AsChar::as_char).eq(str.chars())
        };

        if eq(&self.0, "int") {
            Left(r#"((?:-?\d+)|(?:\d+))"#.chars().map(Ok))
        } else if eq(&self.0, "float") {
            Left(
                r#"((?=.*\d.*)[-+]?\d*(?:\.(?=\d.*))?\d*(?:\d+[E][+-]?\d+)?)"#
                    .chars()
                    .map(Ok),
            )
        } else if eq(&self.0, "word") {
            Left(r#"([^\s]+)"#.chars().map(Ok))
        } else if eq(&self.0, "string") {
            Left(
                r#"("(?:[^"\\]*(?:\\.[^"\\]*)*)"|'(?:[^'\\]*(?:\\.[^'\\]*)*)')"#
                    .chars()
                    .map(Ok),
            )
        } else if eq(&self.0, "") {
            Left(r#"(.*)"#.chars().map(Ok))
        } else {
            Right(iter::once(Err(UnknownParameterError { not_found: self.0 })))
        }
    }
}

/// [`IntoRegexCharIter::Iter`] for [`Parameter`].
type ParameterIter<Input> = Either<
    iter::Map<
        str::Chars<'static>,
        fn(char) -> Result<char, UnknownParameterError<Input>>,
    >,
    iter::Once<Result<char, UnknownParameterError<Input>>>,
>;

/// [`Iterator`] for skipping last [`Item`].
///
/// [`Item`]: Iterator::Item
pub struct SkipLast<Iter: Iterator> {
    /// Inner [`Iterator`] to skip last [`Item`] from.
    ///
    /// [`Item`]: Iterator::Item
    iter: iter::Peekable<Iter>,
}

impl<Iter> Clone for SkipLast<Iter>
where
    Iter: Clone + Iterator,
    Iter::Item: Clone,
{
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
        }
    }
}

impl<Iter> fmt::Debug for SkipLast<Iter>
where
    Iter: fmt::Debug + Iterator,
    Iter::Item: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SkipLast")
            .field("iter", &self.iter)
            .finish()
    }
}

impl<Iter: Iterator> SkipLast<Iter> {
    /// Creates a new [`SkipLast`].
    pub fn new(iter: Iter) -> Self {
        Self {
            iter: iter.peekable(),
        }
    }
}

impl<Iter> Iterator for SkipLast<Iter>
where
    Iter: Iterator,
{
    type Item = Iter::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.iter.next();
        (self.iter.peek().is_some()).then(|| next).flatten()
    }
}

/// [`Iterator`] for escaping `^`, `$`, `[`, `]`, `(`, `)`, `{`, `}`, `.`, `|`,
/// `?`, `*`, `+` with `\` and removing it for other [`char`]s.
///
/// # Example
///
/// ```rust
/// # use cucumber_expressions::expand::EscapeForRegex;
/// #
/// assert_eq!(
///     EscapeForRegex::new("\\\\text\\ (\\)\\".chars()).collect::<String>(),
///     "\\\\text \\(\\)",
/// );
/// ```
#[derive(Clone, Debug)]
pub struct EscapeForRegex<Iter: Iterator> {
    /// Inner [`Iterator`] for escaping.
    iter: iter::Peekable<Iter>,

    /// [`Item`] that was escaped.
    ///
    /// [`Item`]: Iterator::Item
    was_escaped: Option<Iter::Item>,
}

impl<Iter: Iterator> EscapeForRegex<Iter> {
    /// Creates a new [`EscapeForRegex`].
    pub fn new(iter: Iter) -> Self {
        Self {
            iter: iter.peekable(),
            was_escaped: None,
        }
    }
}

impl<Iter> Iterator for EscapeForRegex<Iter>
where
    Iter: Iterator<Item = char>,
{
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        let should_be_escaped = |c| "^$[]()\\{}.|?*+".contains(c);

        if let Some(c) = self.was_escaped.take() {
            return Some(c);
        }

        loop {
            return match self.iter.next() {
                Some('\\') => {
                    let c = *self.iter.peek()?;
                    if should_be_escaped(c) {
                        self.was_escaped = self.iter.next();
                        Some('\\')
                    } else {
                        continue;
                    }
                }
                Some(c) if should_be_escaped(c) => {
                    self.was_escaped = Some(c);
                    Some('\\')
                }
                Some(c) => Some(c),
                None => None,
            };
        }
    }
}

// all tests from https://bit.ly/3C2ONom
#[cfg(test)]
mod spec {
    use super::{ExpansionError as Error, Expression, UnknownParameterError};

    #[test]
    fn alternation_with_optional() {
        assert_eq!(
            Expression::regex("a/b(c)")
                .unwrap_or_else(|e| panic!("failed: {}", e))
                .as_str(),
            "^(?:a|b(?:c)?)$",
        );
    }

    #[test]
    fn alternation() {
        assert_eq!(
            Expression::regex("a/b c/d/e")
                .unwrap_or_else(|e| panic!("failed: {}", e))
                .as_str(),
            "^(?:a|b) (?:c|d|e)$",
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            Expression::regex("")
                .unwrap_or_else(|e| panic!("failed: {}", e))
                .as_str(),
            "^$",
        );
    }

    #[test]
    fn escape_regex_characters() {
        assert_eq!(
            Expression::regex("^$[]\\(\\){}\\\\.|?*+")
                .unwrap_or_else(|e| panic!("failed: {}", e))
                .as_str(),
            "^\\^\\$\\[\\]\\(\\)(.*)\\\\\\.\\|\\?\\*\\+$",
        );
    }

    #[test]
    fn optional() {
        assert_eq!(
            Expression::regex("(a)")
                .unwrap_or_else(|e| panic!("failed: {}", e))
                .as_str(),
            "^(?:a)?$",
        );
    }

    #[test]
    fn parameter() {
        assert_eq!(
            Expression::regex("{int}")
                .unwrap_or_else(|e| panic!("failed: {}", e))
                .as_str(),
            "^((?:-?\\d+)|(?:\\d+))$",
        );
    }

    #[test]
    fn text() {
        assert_eq!(
            Expression::regex("a")
                .unwrap_or_else(|e| panic!("failed: {}", e))
                .as_str(),
            "^a$",
        );
    }

    #[allow(clippy::non_ascii_literal)]
    #[test]
    fn unicode() {
        assert_eq!(
            Expression::regex("Привет, Мир(ы)!")
                .unwrap_or_else(|e| panic!("failed: {}", e))
                .as_str(),
            "^Привет, Мир(?:ы)?!$",
        );
    }

    #[test]
    fn unknown_parameter() {
        match Expression::regex("{custom}").unwrap_err() {
            Error::Expansion(UnknownParameterError { not_found }) => {
                assert_eq!(*not_found, "custom");
            }
            e @ (Error::Parsing(_) | Error::Regex(_)) => {
                panic!("wrong err: {}", e);
            }
        }
    }
}
