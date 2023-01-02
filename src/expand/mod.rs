// Copyright (c) 2021-2023  Brendan Molloy <brendan@bbqsrc.net>,
//                          Ilya Solovyiov <ilya.solovyiov@gmail.com>,
//                          Kai Ren <tyranron@gmail.com>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! [Cucumber Expressions][0] [AST] into [`Regex`] expansion.
//!
//! Follows original [production rules][1].
//!
//! [`Regex`]: regex::Regex
//! [0]: https://github.com/cucumber/cucumber-expressions#readme
//! [1]: https://git.io/J159T
//! [AST]: https://en.wikipedia.org/wiki/Abstract_syntax_tree

pub mod parameters;

use std::{fmt, iter, str, vec};

use derive_more::{Display, Error, From};
use either::Either;
use nom::{AsChar, InputIter};
use regex::Regex;

use crate::{
    parse, Alternation, Alternative, Expression, Optional, Parameter,
    SingleAlternation, SingleExpression, Spanned,
};

pub use self::parameters::{
    Provider as ParametersProvider, WithCustom as WithCustomParameters,
};

#[allow(clippy::multiple_inherent_impl)] // because of `into-regex` feature
impl<'s> Expression<Spanned<'s>> {
    /// Parses the given `input` as an [`Expression`], and immediately expands
    /// it into the appropriate [`Regex`].
    ///
    /// # Parameter types
    ///
    /// Text between curly braces references a *parameter type*.
    /// [Cucumber Expressions][0] come with the following
    /// [built-in parameter types][1]:
    ///
    /// | Parameter Type  | Description                                    |
    /// | --------------- | ---------------------------------------------- |
    /// | `{int}`         | Matches integers                               |
    /// | `{float}`       | Matches floats                                 |
    /// | `{word}`        | Matches words without whitespace               |
    /// | `{string}`      | Matches single-quoted or double-quoted strings |
    /// | `{}` anonymous  | Matches anything (`/.*/`)                      |
    ///
    /// To expand an [`Expression`] with custom parameter types in addition to
    /// the built-in ones, use [`Expression::regex_with_parameters()`].
    ///
    /// # Errors
    ///
    /// See [`Error`] for more details.
    ///
    /// [`Error`]: enum@Error
    /// [0]: https://github.com/cucumber/cucumber-expressions#readme
    /// [1]: https://github.com/cucumber/cucumber-expressions#parameter-types
    pub fn regex<Input: AsRef<str> + ?Sized>(
        input: &'s Input,
    ) -> Result<Regex, Error<Spanned<'s>>> {
        let re_str = Expression::parse(input)?
            .into_regex_char_iter()
            .collect::<Result<String, _>>()?;
        Regex::new(&re_str).map_err(Into::into)
    }

    /// Parses the given `input` as an [`Expression`], and immediately expands
    /// it into the appropriate [`Regex`], considering the custom defined
    /// `parameters` in addition to [default ones][1].
    ///
    /// # Errors
    ///
    /// See [`Error`] for more details.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use std::collections::HashMap;
    /// #
    /// # use cucumber_expressions::Expression;
    /// #
    /// let parameters = HashMap::from([("color", "[Rr]ed|[Gg]reen|[Bb]lue")]);
    /// let re = Expression::regex_with_parameters(
    ///     "{word} has {color} eyes",
    ///     &parameters,
    /// )
    /// .unwrap();
    ///
    /// assert_eq!(
    ///     re.as_str(),
    ///     "^([^\\s]+) has ([Rr]ed|[Gg]reen|[Bb]lue) eyes$",
    /// );
    /// ```
    ///
    /// [`Error`]: enum@Error
    /// [1]: https://github.com/cucumber/cucumber-expressions#parameter-types
    pub fn regex_with_parameters<Input, Parameters>(
        input: &'s Input,
        parameters: Parameters,
    ) -> Result<Regex, Error<Spanned<'s>>>
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

    /// Creates a parser, parsing [`Expression`]s and immediately expanding them
    /// into appropriate [`Regex`]es, considering the custom defined
    /// `parameters` in addition to [default ones][1].
    ///
    /// [1]: https://github.com/cucumber/cucumber-expressions#parameter-types
    pub const fn with_parameters<P: ParametersProvider<Spanned<'s>>>(
        self,
        parameters: P,
    ) -> WithCustomParameters<Self, P> {
        WithCustomParameters {
            element: self,
            parameters,
        }
    }
}

/// Possible errors while parsing `Input` representing a
/// [Cucumber Expression][0] and expanding it into a [`Regex`].
///
/// [0]: https://github.com/cucumber/cucumber-expressions#readme
#[derive(Clone, Debug, Display, Error, From)]
pub enum Error<Input>
where
    Input: fmt::Display,
{
    /// Parsing error.
    #[display(fmt = "Parsing failed: {}", _0)]
    Parsing(parse::Error<Input>),

    /// Expansion error.
    #[display(fmt = "Failed to expand regex: {}", _0)]
    Expansion(ParameterError<Input>),

    /// [`Regex`] creation error.
    #[display(fmt = "Regex creation failed: {}", _0)]
    Regex(regex::Error),
}

/// Possible [`Parameter`] errors being used in an [`Expression`].
#[derive(Clone, Debug, Display, Error)]
pub enum ParameterError<Input>
where
    Input: fmt::Display,
{
    /// [`Parameter`] not found.
    #[display(fmt = "Parameter `{}` not found.", _0)]
    NotFound(Input),

    /// Failed to rename [`Regex`] capturing group.
    #[display(
        fmt = "Failed to rename capturing groups in regex `{}` of \
               parameter `{}`: {}",
        re,
        parameter,
        err
    )]
    RenameRegexGroup {
        /// [`Parameter`] name.
        parameter: Input,

        /// [`Regex`] of the [`Parameter`].
        re: String,

        /// [`Error`] of parsing the [`Regex`] with renamed capturing groups.
        ///
        /// [`Error`]: regex_syntax::Error
        err: Box<regex_syntax::Error>,
    },
}

/// Expansion of a [Cucumber Expressions][0] [AST] element into a [`Regex`] by
/// producing a [`char`]s [`Iterator`] following original [production rules][1].
///
/// [0]: https://github.com/cucumber/cucumber-expressions#readme
/// [1]: https://git.io/J159T
/// [AST]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
pub trait IntoRegexCharIter<Input: fmt::Display> {
    /// Type of an [`Iterator`] performing the expansion.
    type Iter: Iterator<Item = Result<char, ParameterError<Input>>>;

    /// Consumes this [AST] element returning an [`Iterator`] over [`char`]s
    /// transformable into a [`Regex`].
    ///
    /// [AST]: https://github.com/cucumber/cucumber-expressions#readme
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

// TODO: Replace with TAIT, once stabilized:
//       https://github.com/rust-lang/rust/issues/63063
/// [`IntoRegexCharIter::Iter`] for an [`Expression`].
type ExpressionIter<Input> = iter::Chain<
    iter::Chain<
        iter::Once<Result<char, ParameterError<Input>>>,
        iter::FlatMap<
            vec::IntoIter<SingleExpression<Input>>,
            <SingleExpression<Input> as IntoRegexCharIter<Input>>::Iter,
            fn(
                SingleExpression<Input>,
            )
                -> <SingleExpression<Input> as IntoRegexCharIter<Input>>::Iter,
        >,
    >,
    iter::Once<Result<char, ParameterError<Input>>>,
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
            Self::Text(t) | Self::Whitespaces(t) => Right(Right(Right(
                EscapeForRegex::new(t.iter_elements().map(as_char)).map(ok),
            ))),
        }
    }
}

// TODO: Replace with TAIT, once stabilized:
//       https://github.com/rust-lang/rust/issues/63063
/// [`IntoRegexCharIter::Iter`] for a [`SingleExpression`].
type SingleExpressionIter<Input> = Either<
    <Alternation<Input> as IntoRegexCharIter<Input>>::Iter,
    Either<
        <Optional<Input> as IntoRegexCharIter<Input>>::Iter,
        Either<
            <Parameter<Input> as IntoRegexCharIter<Input>>::Iter,
            iter::Map<
                EscapeForRegex<
                    iter::Map<
                        <Input as InputIter>::IterElem,
                        fn(<Input as InputIter>::Item) -> char,
                    >,
                >,
                MapOkChar<Input>,
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

// TODO: Replace with TAIT, once stabilized:
//       https://github.com/rust-lang/rust/issues/63063
/// [`IntoRegexCharIter::Iter`] for an [`Alternation`].
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
    iter::Once<Result<char, ParameterError<I>>>,
>;

// TODO: Replace with TAIT, once stabilized:
//       https://github.com/rust-lang/rust/issues/63063
/// Inner type of an [`AlternationIter`].
type AlternationIterInner<I> = iter::Chain<
    iter::FlatMap<
        vec::IntoIter<Alternative<I>>,
        <Alternative<I> as IntoRegexCharIter<I>>::Iter,
        fn(Alternative<I>) -> <Alternative<I> as IntoRegexCharIter<I>>::Iter,
    >,
    iter::Once<Result<char, ParameterError<I>>>,
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

// TODO: Replace with TAIT, once stabilized:
//       https://github.com/rust-lang/rust/issues/63063
/// [`IntoRegexCharIter::Iter`] for an [`Alternative`].
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

// TODO: Replace with TAIT, once stabilized:
//       https://github.com/rust-lang/rust/issues/63063
/// [`IntoRegexCharIter::Iter`] for an [`Optional`].
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

/// Function pointer describing [`Ok`].
type MapOkChar<Input> = fn(char) -> Result<char, ParameterError<Input>>;

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

        if eq(&self.input, "int") {
            Left(Left(r#"((?:-?\d+)|(?:\d+))"#.chars().map(Ok)))
        } else if eq(&self.input, "float") {
            // Regex in other implementations has lookaheads. As `regex` crate
            // doesn't support them, we use `f32`/`f64` grammar instead:
            // https://doc.rust-lang.org/stable/std/primitive.f64.html#grammar
            // Provided grammar is a superset of the original one:
            // - supports `e` as exponent in addition to `E`
            // - supports trailing comma: `1.`
            // - supports `inf` and `NaN`
            Left(Left(
                "([+-]?(?:inf\
                         |NaN\
                         |(?:\\d+|\\d+\\.\\d*|\\d*\\.\\d+)(?:[eE][+-]?\\d+)?\
                       ))"
                .chars()
                .map(Ok),
            ))
        } else if eq(&self.input, "word") {
            Left(Left(r#"([^\s]+)"#.chars().map(Ok)))
        } else if eq(&self.input, "string") {
            Left(Right(
                OwnedChars::new(format!(
                    "(?:\
                      \"(?P<__{id}_0>[^\"\\\\]*(?:\\\\.[^\"\\\\]*)*)\"\
                      |'(?P<__{id}_1>[^'\\\\]*(?:\\\\.[^'\\\\]*)*)'\
                    )",
                    id = self.id,
                ))
                .map(Ok),
            ))
        } else if eq(&self.input, "") {
            Left(Left(r#"(.*)"#.chars().map(Ok)))
        } else {
            Right(iter::once(Err(ParameterError::NotFound(self.input))))
        }
    }
}

// TODO: Replace with TAIT, once stabilized:
//       https://github.com/rust-lang/rust/issues/63063
/// [`IntoRegexCharIter::Iter`] for a [`Parameter`].
type ParameterIter<Input> = Either<
    Either<
        iter::Map<
            str::Chars<'static>,
            fn(char) -> Result<char, ParameterError<Input>>,
        >,
        iter::Map<OwnedChars, fn(char) -> Result<char, ParameterError<Input>>>,
    >,
    iter::Once<Result<char, ParameterError<Input>>>,
>;

/// [`Iterator`] for skipping a last [`Item`].
///
/// [`Item`]: Iterator::Item
pub struct SkipLast<Iter: Iterator> {
    /// Inner [`Iterator`] to skip the last [`Item`] from.
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
    /// Creates a new [`SkipLast`] [`Iterator`].
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
        (self.iter.peek().is_some()).then_some(next).flatten()
    }
}

// TODO: Make private, once TAIT stabilized:
//       https://github.com/rust-lang/rust/issues/63063
/// Like [`str::Chars`] [`Iterator`], but owns its [`String`].
#[derive(Clone, Debug)]
pub struct OwnedChars {
    /// Iterated [`String`].
    str: String,

    /// Current char number.
    cur: usize,
}

impl OwnedChars {
    /// Creates a new [`OwnedChars`] [`Iterator`].
    #[must_use]
    pub const fn new(str: String) -> Self {
        Self { str, cur: 0 }
    }
}

impl Iterator for OwnedChars {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        let char = self.str.chars().nth(self.cur)?;
        self.cur += 1;
        Some(char)
    }
}

/// [`Iterator`] for escaping `^`, `$`, `[`, `]`, `(`, `)`, `{`, `}`, `.`, `|`,
/// `?`, `*`, `+` with `\`, and removing it for other [`char`]s.
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
    /// Creates a new [`EscapeForRegex`] [`Iterator`].
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

        if self.was_escaped.is_some() {
            return self.was_escaped.take();
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

// All test examples from: <https://git.io/J159G>
// Naming of test cases is preserved.
#[cfg(test)]
mod spec {
    use super::{Error, Expression, ParameterError};

    #[test]
    fn alternation_with_optional() {
        let expr = Expression::regex("a/b(c)")
            .unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(expr.as_str(), "^(?:a|b(?:c)?)$");
    }

    #[test]
    fn alternation() {
        let expr = Expression::regex("a/b c/d/e")
            .unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(expr.as_str(), "^(?:a|b) (?:c|d|e)$");
        assert!(expr.is_match("a c"));
        assert!(expr.is_match("b e"));
        assert!(!expr.is_match("c e"));
        assert!(!expr.is_match("a"));
        assert!(!expr.is_match("a "));
    }

    #[test]
    fn empty() {
        let expr =
            Expression::regex("").unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(expr.as_str(), "^$");
        assert!(expr.is_match(""));
        assert!(!expr.is_match("a"));
    }

    #[test]
    fn escape_regex_characters() {
        let expr = Expression::regex(r"^$[]\()\{}\\.|?*+")
            .unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(expr.as_str(), r"^\^\$\[\]\(\)\{\}\\\.\|\?\*\+$");
        assert!(expr.is_match("^$[](){}\\.|?*+"));
    }

    #[test]
    fn optional() {
        let expr =
            Expression::regex("(a)").unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(expr.as_str(), "^(?:a)?$");
        assert!(expr.is_match(""));
        assert!(expr.is_match("a"));
        assert!(!expr.is_match("b"));
    }

    #[test]
    fn parameter_int() {
        let expr = Expression::regex("{int}")
            .unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(expr.as_str(), "^((?:-?\\d+)|(?:\\d+))$");
        assert!(expr.is_match("123"));
        assert!(expr.is_match("-123"));
        assert!(!expr.is_match("+123"));
        assert!(!expr.is_match("123."));
    }

    #[test]
    fn parameter_float() {
        let expr = Expression::regex("{float}")
            .unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(
            expr.as_str(),
            "^([+-]?(?:inf\
                      |NaN\
                      |(?:\\d+|\\d+\\.\\d*|\\d*\\.\\d+)(?:[eE][+-]?\\d+)?\
                    ))$",
        );
        assert!(expr.is_match("+1"));
        assert!(expr.is_match(".1"));
        assert!(expr.is_match("-.1"));
        assert!(expr.is_match("-1."));
        assert!(expr.is_match("-1.1E+1"));
        assert!(expr.is_match("-inf"));
        assert!(expr.is_match("NaN"));
    }

    #[test]
    fn parameter_word() {
        let expr = Expression::regex("{word}")
            .unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(expr.as_str(), "^([^\\s]+)$");
        assert!(expr.is_match("test"));
        assert!(expr.is_match("\"test\""));
        assert!(!expr.is_match("with space"));
    }

    #[test]
    fn parameter_string() {
        let expr = Expression::regex("{string}")
            .unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(
            expr.as_str(),
            "^(?:\
                \"(?P<__0_0>[^\"\\\\]*(?:\\\\.[^\"\\\\]*)*)\"\
                |'(?P<__0_1>[^'\\\\]*(?:\\\\.[^'\\\\]*)*)'\
             )$",
        );
        assert!(expr.is_match("\"\""));
        assert!(expr.is_match("''"));
        assert!(expr.is_match("'with \"'"));
        assert!(expr.is_match("\"with '\""));
        assert!(expr.is_match("\"with \\\" escaped\""));
        assert!(expr.is_match("'with \\' escaped'"));
        assert!(!expr.is_match("word"));
    }

    #[test]
    fn multiple_string_parameters() {
        let expr = Expression::regex("{string} {string}")
            .unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(
            expr.as_str(),
            "^(?:\
                \"(?P<__0_0>[^\"\\\\]*(?:\\\\.[^\"\\\\]*)*)\"\
                |'(?P<__0_1>[^'\\\\]*(?:\\\\.[^'\\\\]*)*)'\
              ) (?:\
                \"(?P<__1_0>[^\"\\\\]*(?:\\\\.[^\"\\\\]*)*)\"\
                |'(?P<__1_1>[^'\\\\]*(?:\\\\.[^'\\\\]*)*)'\
              )$",
        );
        assert!(expr.is_match("\"\" ''"));
        assert!(expr.is_match("'' \"\""));
        assert!(expr.is_match("'with \"' \"\""));
        assert!(expr.is_match("\"with '\" '\"'"));
        assert!(expr.is_match("\"with \\\" escaped\" 'with \\' escaped'"));
        assert!(expr.is_match("'with \\' escaped' \"with \\\" escaped\""));
    }

    #[test]
    fn parameter_all() {
        let expr =
            Expression::regex("{}").unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(expr.as_str(), "^(.*)$");
        assert!(expr.is_match("anything matches"));
    }

    #[test]
    fn text() {
        let expr =
            Expression::regex("a").unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(expr.as_str(), "^a$");
        assert!(expr.is_match("a"));
        assert!(!expr.is_match("b"));
        assert!(!expr.is_match("ab"));
    }

    #[test]
    fn unicode() {
        let expr = Expression::regex("Привет, Мир(ы)!")
            .unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(expr.as_str(), "^Привет, Мир(?:ы)?!$");
        assert!(expr.is_match("Привет, Мир!"));
        assert!(expr.is_match("Привет, Миры!"));
        assert!(!expr.is_match("Hello world"));
    }

    #[test]
    fn unknown_parameter() {
        match Expression::regex("{custom}").unwrap_err() {
            Error::Expansion(ParameterError::NotFound(not_found)) => {
                assert_eq!(*not_found, "custom");
            }
            e @ (Error::Parsing(_) | Error::Regex(_) | Error::Expansion(_)) => {
                panic!("wrong err: {e}");
            }
        }
    }
}
