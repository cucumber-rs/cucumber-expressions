// Copyright (c) 2021-2023  Brendan Molloy <brendan@bbqsrc.net>,
//                          Ilya Solovyiov <ilya.solovyiov@gmail.com>,
//                          Kai Ren <tyranron@gmail.com>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! [Cucumber Expressions][1] [AST] parser.
//!
//! See details in the [grammar spec][0].
//!
//! [0]: crate#grammar
//! [1]: https://github.com/cucumber/cucumber-expressions#readme
//! [AST]: https://en.wikipedia.org/wiki/Abstract_syntax_tree

use std::{fmt::Display, ops::RangeFrom};

use derive_more::{Display, Error};
use nom::{
    branch::alt,
    bytes::complete::{tag, take_while, take_while1},
    character::complete::one_of,
    combinator::{map, peek, verify},
    error::{ErrorKind, ParseError},
    multi::{many0, many1, separated_list1},
    sequence::tuple,
    AsChar, Compare, Err, FindToken, IResult, InputIter, InputLength,
    InputTake, InputTakeAtPosition, Needed, Offset, Parser, Slice,
};

use crate::{
    ast::{
        Alternation, Alternative, Expression, Optional, Parameter,
        SingleExpression,
    },
    combinator,
};

/// Reserved characters requiring a special handling.
pub const RESERVED_CHARS: &str = r#"{}()\/ "#;

/// Matches `normal` and [`RESERVED_CHARS`] escaped with `\`.
///
/// Uses [`combinator::escaped0`] under the hood.
///
/// # Errors
///
/// ## Recoverable [`Error`]
///
/// - If `normal` parser errors.
///
/// ## Irrecoverable [`Failure`]
///
/// - If `normal` parser fails.
/// - [`EscapedEndOfLine`].
/// - [`EscapedNonReservedCharacter`].
///
/// [`Error`]: Err::Error
/// [`EscapedEndOfLine`]: Error::EscapedEndOfLine
/// [`EscapedNonReservedCharacter`]: Error::EscapedNonReservedCharacter
/// [`Failure`]: Err::Failure
fn escaped_reserved_chars0<'a, Input: 'a, F, O1>(
    normal: F,
) -> impl FnMut(Input) -> IResult<Input, Input, Error<Input>>
where
    Input: Clone
        + Display
        + Offset
        + InputLength
        + InputTake
        + InputTakeAtPosition
        + Slice<RangeFrom<usize>>
        + InputIter,
    <Input as InputIter>::Item: AsChar + Copy,
    F: Parser<Input, O1, Error<Input>>,
    Error<Input>: ParseError<Input>,
    for<'s> &'s str: FindToken<<Input as InputIter>::Item>,
{
    combinator::map_err(
        combinator::escaped0(normal, '\\', one_of(RESERVED_CHARS)),
        |e| {
            if let Err::Error(Error::Other(span, ErrorKind::Escaped)) = e {
                match span.input_len() {
                    1 => Error::EscapedEndOfLine(span),
                    n if n > 1 => Error::EscapedNonReservedCharacter(
                        span.take(span.slice_index(2).unwrap_or_default()),
                    ),
                    _ => Error::EscapedNonReservedCharacter(span),
                }
                .failure()
            } else {
                e
            }
        },
    )
}

/// Parses a `parameter` as defined in the [grammar spec][0].
///
/// # Grammar
///
/// ```ebnf
/// parameter       = '{', name*, '}'
/// name            = (- name-to-escape) | ('\', name-to-escape)
/// name-to-escape  = '{' | '}' | '(' | '/' | '\'
/// ```
///
/// # Example
///
/// ```text
/// {}
/// {name}
/// {with spaces}
/// {escaped \/\{\(}
/// {no need to escape )}
/// {🦀}
/// ```
///
/// # Errors
///
/// ## Recoverable [`Error`]
///
/// - If `input` doesn't start with `{`.
///
/// ## Irrecoverable [`Failure`].
///
/// - [`EscapedNonReservedCharacter`].
/// - [`NestedParameter`].
/// - [`OptionalInParameter`].
/// - [`UnescapedReservedCharacter`].
/// - [`UnfinishedParameter`].
///
/// # Indexing
///
/// The given `indexer` is incremented only if the parsed [`Parameter`] is
/// returned.
///
/// [`Error`]: Err::Error
/// [`Failure`]: Err::Failure
/// [`EscapedNonReservedCharacter`]: Error::EscapedNonReservedCharacter
/// [`NestedParameter`]: Error::NestedParameter
/// [`OptionalInParameter`]: Error::OptionalInParameter
/// [`UnescapedReservedCharacter`]: Error::UnescapedReservedCharacter
/// [`UnfinishedParameter`]: Error::UnfinishedParameter
/// [0]: crate#grammar
pub fn parameter<'a, Input: 'a>(
    input: Input,
    indexer: &mut usize,
) -> IResult<Input, Parameter<Input>, Error<Input>>
where
    Input: Clone
        + Display
        + Offset
        + InputLength
        + InputTake
        + InputTakeAtPosition<Item = char>
        + Slice<RangeFrom<usize>>
        + InputIter
        + for<'s> Compare<&'s str>,
    <Input as InputIter>::Item: AsChar + Copy,
    Error<Input>: ParseError<Input>,
    for<'s> &'s str: FindToken<<Input as InputIter>::Item>,
{
    let is_name = |c| !"{}(\\/".contains(c);

    let fail = |inp: Input, opening_brace| {
        match inp.iter_elements().next().map(AsChar::as_char) {
            Some('{') => {
                if let Ok((_, (par, ..))) = peek(tuple((
                    // We don't use `indexer` here, because we do this parsing
                    // for error reporting only.
                    |i| parameter(i, &mut 0),
                    escaped_reserved_chars0(take_while(is_name)),
                    tag("}"),
                )))(inp.clone())
                {
                    return Error::NestedParameter(
                        inp.take(par.input.input_len() + 2),
                    )
                    .failure();
                }
                return Error::UnescapedReservedCharacter(inp.take(1))
                    .failure();
            }
            Some('(') => {
                if let Ok((_, opt)) = peek(optional)(inp.clone()) {
                    return Error::OptionalInParameter(
                        inp.take(opt.0.input_len() + 2),
                    )
                    .failure();
                }
                return Error::UnescapedReservedCharacter(inp.take(1))
                    .failure();
            }
            Some(c) if RESERVED_CHARS.contains(c) => {
                return Error::UnescapedReservedCharacter(inp.take(1))
                    .failure();
            }
            _ => {}
        }
        Error::UnfinishedParameter(opening_brace).failure()
    };

    let (input, opening_brace) = tag("{")(input)?;
    let (input, par_name) =
        escaped_reserved_chars0(take_while(is_name))(input)?;
    let (input, _) = combinator::map_err(tag("}"), |_| {
        fail(input.clone(), opening_brace.clone())
    })(input.clone())?;

    *indexer += 1;
    Ok((
        input,
        Parameter {
            input: par_name,
            id: *indexer - 1,
        },
    ))
}

/// Parses an `optional` as defined in the [grammar spec][0].
///
/// # Grammar
///
/// ```ebnf
/// optional           = '(' text-in-optional+ ')'
/// text-in-optional   = (- optional-to-escape) | ('\', optional-to-escape)
/// optional-to-escape = '(' | ')' | '{' | '/' | '\'
/// ```
///
/// # Example
///
/// ```text
/// (name)
/// (with spaces)
/// (escaped \/\{\()
/// (no need to escape })
/// (🦀)
/// ```
///
/// # Errors
///
/// ## Recoverable [`Error`]
///
/// - If `input` doesn't start with `(`.
///
/// ## Irrecoverable [`Failure`]
///
/// - [`AlternationInOptional`].
/// - [`EmptyOptional`].
/// - [`EscapedEndOfLine`].
/// - [`EscapedNonReservedCharacter`].
/// - [`NestedOptional`].
/// - [`ParameterInOptional`].
/// - [`UnescapedReservedCharacter`].
/// - [`UnfinishedOptional`].
///
/// [`Error`]: Err::Error
/// [`Failure`]: Err::Failure
/// [`AlternationInOptional`]: Error::AlternationInOptional
/// [`EmptyOptional`]: Error::EmptyOptional
/// [`EscapedEndOfLine`]: Error::EscapedEndOfLine
/// [`EscapedNonReservedCharacter`]: Error::EscapedNonReservedCharacter
/// [`NestedOptional`]: Error::NestedOptional
/// [`ParameterInOptional`]: Error::ParameterInOptional
/// [`UnescapedReservedCharacter`]: Error::UnescapedReservedCharacter
/// [`UnfinishedOptional`]: Error::UnfinishedOptional
/// [0]: crate#grammar
pub fn optional<'a, Input: 'a>(
    input: Input,
) -> IResult<Input, Optional<Input>, Error<Input>>
where
    Input: Clone
        + Display
        + Offset
        + InputLength
        + InputTake
        + InputTakeAtPosition<Item = char>
        + Slice<RangeFrom<usize>>
        + InputIter
        + for<'s> Compare<&'s str>,
    <Input as InputIter>::Item: AsChar + Copy,
    Error<Input>: ParseError<Input>,
    for<'s> &'s str: FindToken<<Input as InputIter>::Item>,
{
    let is_in_optional = |c| !"(){\\/".contains(c);

    let fail = |inp: Input, opening_brace| {
        match inp.iter_elements().next().map(AsChar::as_char) {
            Some('(') => {
                if let Ok((_, (opt, ..))) = peek(tuple((
                    optional,
                    escaped_reserved_chars0(take_while(is_in_optional)),
                    tag(")"),
                )))(inp.clone())
                {
                    return Error::NestedOptional(
                        inp.take(opt.0.input_len() + 2),
                    )
                    .failure();
                }
                return Error::UnescapedReservedCharacter(inp.take(1))
                    .failure();
            }
            Some('{') => {
                // We use just `0` as `indexer` here, because we do this parsing
                // for error reporting only.
                if let Ok((_, par)) =
                    peek(|i| parameter(i, &mut 0))(inp.clone())
                {
                    return Error::ParameterInOptional(
                        inp.take(par.input.input_len() + 2),
                    )
                    .failure();
                }
                return Error::UnescapedReservedCharacter(inp.take(1))
                    .failure();
            }
            Some('/') => {
                return Error::AlternationInOptional(inp.take(1)).failure();
            }
            Some(c) if RESERVED_CHARS.contains(c) => {
                return Error::UnescapedReservedCharacter(inp.take(1))
                    .failure();
            }
            _ => {}
        }
        Error::UnfinishedOptional(opening_brace).failure()
    };

    let original_input = input.clone();
    let (input, opening_paren) = tag("(")(input)?;
    let (input, opt) =
        escaped_reserved_chars0(take_while(is_in_optional))(input)?;
    let (input, _) = combinator::map_err(tag(")"), |_| {
        fail(input.clone(), opening_paren.clone())
    })(input.clone())?;

    if opt.input_len() == 0 {
        return Err(Err::Failure(Error::EmptyOptional(original_input.take(2))));
    }

    Ok((input, Optional(opt)))
}

/// Parses an `alternative` as defined in the [grammar spec][0].
///
/// # Grammar
///
/// ```ebnf
/// alternative           = optional | (text-in-alternative+)
/// text-in-alternative   = (- alternative-to-escape)
///                          | ('\', alternative-to-escape)
/// alternative-to-escape = ' ' | '(' | '{' | '/' | '\'
/// ```
///
/// # Example
///
/// ```text
/// text
/// escaped\ whitespace
/// no-need-to-escape)}
/// 🦀
/// (optional)
/// ```
///
/// # Errors
///
/// ## Irrecoverable [`Failure`]
///
/// Any [`Failure`] of [`optional()`].
///
/// [`Failure`]: Err::Failure
/// [0]: crate#grammar
pub fn alternative<'a, Input: 'a>(
    input: Input,
) -> IResult<Input, Alternative<Input>, Error<Input>>
where
    Input: Clone
        + Display
        + Offset
        + InputLength
        + InputTake
        + InputTakeAtPosition<Item = char>
        + Slice<RangeFrom<usize>>
        + InputIter
        + for<'s> Compare<&'s str>,
    <Input as InputIter>::Item: AsChar + Copy,
    Error<Input>: ParseError<Input>,
    for<'s> &'s str: FindToken<<Input as InputIter>::Item>,
{
    let is_without_whitespace = |c| !" ({\\/".contains(c);

    alt((
        map(optional, Alternative::Optional),
        map(
            verify(
                escaped_reserved_chars0(take_while(is_without_whitespace)),
                |p| p.input_len() > 0,
            ),
            Alternative::Text,
        ),
    ))(input)
}

/// Parses an `alternation` as defined in the [grammar spec][0].
///
/// # Grammar
///
/// ```ebnf
/// alternation        = single-alternation, (`/`, single-alternation)+
/// single-alternation = ((text-in-alternative+, optional*)
///                        | (optional+, text-in-alternative+))+
/// ```
///
/// # Example
///
/// ```text
/// left/right
/// left(opt)/(opt)right
/// escaped\ /text
/// no-need-to-escape)}/text
/// 🦀/⚙️
/// ```
///
/// # Errors
///
/// ## Recoverable [`Error`]
///
/// - If `input` doesn't have `/`.
///
/// ## Irrecoverable [`Failure`]
///
/// - Any [`Failure`] of [`optional()`].
/// - [`EmptyAlternation`].
/// - [`OnlyOptionalInAlternation`].
///
/// [`Error`]: Err::Error
/// [`Failure`]: Err::Failure
/// [`EmptyAlternation`]: Error::EmptyAlternation
/// [`OnlyOptionalInAlternation`]: Error::OnlyOptionalInAlternation
/// [0]: crate#grammar
pub fn alternation<Input>(
    input: Input,
) -> IResult<Input, Alternation<Input>, Error<Input>>
where
    Input: Clone
        + Display
        + Offset
        + InputLength
        + InputTake
        + InputTakeAtPosition<Item = char>
        + Slice<RangeFrom<usize>>
        + InputIter
        + for<'s> Compare<&'s str>,
    <Input as InputIter>::Item: AsChar + Copy,
    Error<Input>: ParseError<Input>,
    for<'s> &'s str: FindToken<<Input as InputIter>::Item>,
{
    let original_input = input.clone();
    let (rest, alt) = match separated_list1(tag("/"), many1(alternative))(input)
    {
        Ok((rest, alt)) => {
            if let Ok((_, slash)) =
                peek::<_, _, Error<Input>, _>(tag("/"))(rest.clone())
            {
                Err(Error::EmptyAlternation(slash).failure())
            } else if alt.len() == 1 {
                Err(Err::Error(Error::Other(rest, ErrorKind::Tag)))
            } else {
                Ok((rest, Alternation(alt)))
            }
        }
        Err(Err::Error(Error::Other(sp, ErrorKind::Many1)))
            if peek::<_, _, Error<Input>, _>(tag("/"))(sp.clone()).is_ok() =>
        {
            Err(Error::EmptyAlternation(sp.take(1)).failure())
        }
        Err(e) => Err(e),
    }?;

    alt.contains_only_optional()
        .then(|| {
            Err(Error::OnlyOptionalInAlternation(
                original_input.take(alt.span_len()),
            )
            .failure())
        })
        .unwrap_or(Ok((rest, alt)))
}

/// Parses a `single-expression` as defined in the [grammar spec][0].
///
/// # Grammar
///
/// ```ebnf
/// single-expression       = alternation
///                            | optional
///                            | parameter
///                            | text-without-whitespace+
///                            | whitespace+
/// text-without-whitespace = (- (text-to-escape | whitespace))
///                            | ('\', text-to-escape)
/// text-to-escape          = '(' | '{' | '/' | '\'
/// ```
///
/// # Example
///
/// ```text
/// text(opt)/text
/// (opt)
/// {string}
/// text
/// ```
///
/// # Errors
///
/// ## Irrecoverable [`Failure`]
///
/// Any [`Failure`] of [`alternation()`], [`optional()`] or [`parameter()`].
///
/// # Indexing
///
/// The given `indexer` is incremented only if the parsed [`SingleExpression`]
/// is returned and it represents a [`Parameter`].
///
/// [`Failure`]: Err::Failure
/// [0]: crate#grammar
pub fn single_expression<'a, Input: 'a>(
    input: Input,
    indexer: &mut usize,
) -> IResult<Input, SingleExpression<Input>, Error<Input>>
where
    Input: Clone
        + Display
        + Offset
        + InputLength
        + InputTake
        + InputTakeAtPosition<Item = char>
        + Slice<RangeFrom<usize>>
        + InputIter
        + for<'s> Compare<&'s str>,
    <Input as InputIter>::Item: AsChar + Copy,
    Error<Input>: ParseError<Input>,
    for<'s> &'s str: FindToken<<Input as InputIter>::Item>,
{
    let is_without_whitespace = |c| !" ({\\/".contains(c);
    let is_whitespace = |c| c == ' ';

    alt((
        map(alternation, SingleExpression::Alternation),
        map(optional, SingleExpression::Optional),
        map(|i| parameter(i, indexer), SingleExpression::Parameter),
        map(
            verify(
                escaped_reserved_chars0(take_while(is_without_whitespace)),
                |s| s.input_len() > 0,
            ),
            SingleExpression::Text,
        ),
        map(take_while1(is_whitespace), SingleExpression::Whitespaces),
    ))(input)
}

/// Parses an `expression` as defined in the [grammar spec][0].
///
/// # Grammar
///
/// ```ebnf
/// expression = single-expression*
/// ```
///
/// # Example
///
/// ```text
/// text(opt)/text
/// (opt)
/// {string}
/// text
/// ```
///
/// > **NOTE:** Empty string is matched too.
///
/// # Errors
///
/// ## Irrecoverable [`Failure`]
///
/// Any [`Failure`] of [`alternation()`], [`optional()`] or [`parameter()`].
///
/// [`Failure`]: Err::Failure
/// [0]: crate#grammar
pub fn expression<'a, Input: 'a>(
    input: Input,
) -> IResult<Input, Expression<Input>, Error<Input>>
where
    Input: Clone
        + Display
        + Offset
        + InputLength
        + InputTake
        + InputTakeAtPosition<Item = char>
        + Slice<RangeFrom<usize>>
        + InputIter
        + for<'s> Compare<&'s str>,
    <Input as InputIter>::Item: AsChar + Copy,
    Error<Input>: ParseError<Input>,
    for<'s> &'s str: FindToken<<Input as InputIter>::Item>,
{
    let mut indexer = 0;
    map(
        many0(move |i| single_expression(i, &mut indexer)),
        Expression,
    )(input)
}

/// Possible parsing errors.
#[derive(Clone, Copy, Debug, Display, Error, Eq, PartialEq)]
pub enum Error<Input>
where
    Input: Display,
{
    /// Nested [`Parameter`]s.
    #[display(
        fmt = "{}\n\
               A parameter may not contain an other parameter.\n\
               If you did not mean to use an optional type you can use '\\{{' \
               to escape the '{{'. For more complicated expressions consider \
               using a regular expression instead.",
        _0
    )]
    NestedParameter(#[error(not(source))] Input),

    /// [`Optional`] inside a [`Parameter`].
    #[display(
        fmt = "{}\n\
               A parameter may not contain an optional.\n\
               If you did not mean to use an parameter type you can use '\\(' \
               to escape the '('.",
        _0
    )]
    OptionalInParameter(#[error(not(source))] Input),

    /// Unfinished [`Parameter`].
    #[display(
        fmt = "{}\n\
               The '{{' does not have a matching '}}'.\n\
               If you did not intend to use a parameter you can use '\\{{' to \
               escape the '{{'.",
        _0
    )]
    UnfinishedParameter(#[error(not(source))] Input),

    /// Nested [`Optional`].
    #[display(
        fmt = "{}\n\
               An optional may not contain an other optional.\n\
               If you did not mean to use an optional type you can use '\\(' \
               to escape the '('. For more complicated expressions consider \
               using a regular expression instead.",
        _0
    )]
    NestedOptional(#[error(not(source))] Input),

    /// [`Parameter`] inside an [`Optional`].
    #[display(
        fmt = "{}\n\
               An optional may not contain a parameter.\n\
               If you did not mean to use an parameter type you can use \
               '\\{{' to escape the '{{'.",
        _0
    )]
    ParameterInOptional(#[error(not(source))] Input),

    /// Empty [`Optional`].
    #[display(
        fmt = "{}\n\
               An optional must contain some text.\n\
               If you did not mean to use an optional you can use '\\(' to \
               escape the '('.",
        _0
    )]
    EmptyOptional(#[error(not(source))] Input),

    /// [`Alternation`] inside an [`Optional`].
    #[display(
        fmt = "{}\n\
               An alternation can not be used inside an optional.\n\
               You can use '\\/' to escape the '/'.",
        _0
    )]
    AlternationInOptional(#[error(not(source))] Input),

    /// Unfinished [`Optional`].
    #[display(
        fmt = "{}\n\
               The '(' does not have a matching ')'.\n\
               If you did not intend to use an optional you can use '\\(' to \
               escape the '('.",
        _0
    )]
    UnfinishedOptional(#[error(not(source))] Input),

    /// Empty [`Alternation`].
    #[display(
        fmt = "{}\n\
               An alternation can not be empty.\n\
               If you did not mean to use an alternative you can use '\\/' to \
               escape the '/'.",
        _0
    )]
    EmptyAlternation(#[error(not(source))] Input),

    /// Only [`Optional`] inside [`Alternation`].
    #[display(
        fmt = "{}\n\
               An alternation may not exclusively contain optionals.\n\
               If you did not mean to use an optional you can use '\\(' to \
               escape the '('.",
        _0
    )]
    OnlyOptionalInAlternation(#[error(not(source))] Input),

    /// Unescaped [`RESERVED_CHARS`].
    #[display(
        fmt = "{}\n\
               Unescaped reserved character.\n\
               You can use an '\\' to escape it.",
        _0
    )]
    UnescapedReservedCharacter(#[error(not(source))] Input),

    /// Escaped non-[`RESERVED_CHARS`].
    #[display(
        fmt = "{}\n\
               Only the characters '{{', '}}', '(', ')', '\\', '/' and \
               whitespace can be escaped.\n\
               If you did mean to use an '\\' you can use '\\\\' to escape it.",
        _0
    )]
    EscapedNonReservedCharacter(#[error(not(source))] Input),

    /// Escaped EOL.
    #[display(
        fmt = "{}\n\
               The end of line can not be escaped.\n\
               You can use '\\' to escape the the '\'.",
        _0
    )]
    EscapedEndOfLine(#[error(not(source))] Input),

    /// Unknown error.
    #[display(
        fmt = "{}\n\
               Unknown parsing error.",
        _0
    )]
    Other(#[error(not(source))] Input, ErrorKind),

    /// Parsing requires more data.
    #[display(
        fmt = "{}",
        "match _0 {\
            Needed::Size(n) => format!(\"Parsing requires {n} bytes/chars\"),\
            Needed::Unknown => \"Parsing requires more data\".to_owned(),\
        }"
    )]
    Needed(#[error(not(source))] Needed),
}

impl<Input: Display> Error<Input> {
    /// Converts this [`Error`] into a [`Failure`].
    ///
    /// [`Error`]: enum@Error
    /// [`Failure`]: Err::Failure
    const fn failure(self) -> Err<Self> {
        Err::Failure(self)
    }
}

impl<Input: Display> ParseError<Input> for Error<Input> {
    fn from_error_kind(input: Input, kind: ErrorKind) -> Self {
        Self::Other(input, kind)
    }

    fn append(input: Input, kind: ErrorKind, other: Self) -> Self {
        if let Self::Other(..) = other {
            Self::from_error_kind(input, kind)
        } else {
            other
        }
    }
}

#[cfg(test)]
mod spec {
    use std::fmt;

    use nom::{error::ErrorKind, Err, IResult};

    use crate::{
        parse::{
            alternation, alternative, expression, optional, parameter, Error,
        },
        Alternative, Spanned,
    };

    /// Asserts two given text representations of [AST] to be equal.
    ///
    /// [AST]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
    fn assert_ast_eq(actual: impl fmt::Debug, expected: impl AsRef<str>) {
        assert_eq!(
            format!("{actual:#?}")
                .lines()
                .map(|line| line.trim_start().trim_end_matches('\n'))
                .collect::<String>(),
            expected
                .as_ref()
                .lines()
                .map(|line| line.trim_end_matches('\n').trim())
                .collect::<String>(),
        );
    }

    /// Unwraps the given `parser` result asserting it has finished and succeed.
    fn unwrap_parser<'s, T>(
        parser: IResult<Spanned<'s>, T, Error<Spanned<'s>>>,
    ) -> T {
        let (rest, par) =
            parser.unwrap_or_else(|e| panic!("Expected Ok, found Err: {e}"));
        assert_eq!(*rest, "");
        par
    }

    mod parameter {
        use super::{parameter, unwrap_parser, Err, Error, ErrorKind, Spanned};

        #[test]
        fn empty() {
            assert_eq!(
                **unwrap_parser(parameter(Spanned::new("{}"), &mut 0)),
                "",
            );
        }

        #[test]
        fn named() {
            assert_eq!(
                **unwrap_parser(parameter(Spanned::new("{string}"), &mut 0)),
                "string",
            );
        }

        #[test]
        fn named_with_spaces() {
            assert_eq!(
                **unwrap_parser(parameter(
                    Spanned::new("{with space}"),
                    &mut 0,
                )),
                "with space",
            );
        }

        #[test]
        fn named_with_escaped() {
            assert_eq!(
                **unwrap_parser(parameter(Spanned::new("{with \\{}"), &mut 0)),
                "with \\{",
            );
        }

        #[test]
        fn named_with_closing_paren() {
            assert_eq!(
                **unwrap_parser(parameter(Spanned::new("{with )}"), &mut 0)),
                "with )",
            );
        }

        #[test]
        fn named_with_emoji() {
            assert_eq!(
                **unwrap_parser(parameter(Spanned::new("{🦀}"), &mut 0)),
                "🦀",
            );
        }

        #[test]
        fn errors_on_empty() {
            let span = Spanned::new("");

            assert_eq!(
                parameter(span, &mut 0),
                Err(Err::Error(Error::Other(span, ErrorKind::Tag))),
            );
        }

        #[test]
        fn fails_on_escaped_non_reserved() {
            let err = parameter(Spanned::new("{\\r}"), &mut 0).unwrap_err();

            match err {
                Err::Failure(Error::EscapedNonReservedCharacter(e)) => {
                    assert_eq!(*e, "\\r");
                }
                Err::Incomplete(_) | Err::Error(_) | Err::Failure(_) => {
                    panic!("wrong error: {err:?}");
                }
            }
        }

        #[test]
        fn fails_on_nested() {
            for input in [
                "{{nest}}",
                "{before{nest}}",
                "{{nest}after}",
                "{bef{nest}aft}",
            ] {
                match parameter(Spanned::new(input), &mut 0).expect_err("error")
                {
                    Err::Failure(Error::NestedParameter(e)) => {
                        assert_eq!(*e, "{nest}", "on input: {input}");
                    }
                    e => panic!("wrong error: {e:?}"),
                }
            }
        }

        #[test]
        fn fails_on_optional() {
            for input in [
                "{(nest)}",
                "{before(nest)}",
                "{(nest)after}",
                "{bef(nest)aft}",
            ] {
                match parameter(Spanned::new(input), &mut 0).expect_err("error")
                {
                    Err::Failure(Error::OptionalInParameter(e)) => {
                        assert_eq!(*e, "(nest)", "on input: {input}");
                    }
                    e => panic!("wrong error: {e:?}"),
                }
            }
        }

        #[test]
        fn fails_on_unescaped_reserved_char() {
            for (input, expected) in [
                ("{(opt}", "("),
                ("{(n(e)st)}", "("),
                ("{{nest}", "{"),
                ("{l/r}", "/"),
            ] {
                match parameter(Spanned::new(input), &mut 0).expect_err("error")
                {
                    Err::Failure(Error::UnescapedReservedCharacter(e)) => {
                        assert_eq!(*e, expected, "on input: {input}");
                    }
                    e => panic!("wrong error: {e:?}"),
                }
            }
        }

        #[test]
        fn fails_on_unfinished() {
            for input in ["{", "{name "] {
                match parameter(Spanned::new(input), &mut 0).expect_err("error")
                {
                    Err::Failure(Error::UnfinishedParameter(e)) => {
                        assert_eq!(*e, "{", "on input: {input}");
                    }
                    e => panic!("wrong error: {e:?}"),
                }
            }
        }
    }

    mod optional {
        use super::{optional, unwrap_parser, Err, Error, ErrorKind, Spanned};

        #[test]
        fn basic() {
            assert_eq!(
                **unwrap_parser(optional(Spanned::new("(string)"))),
                "string",
            );
        }

        #[test]
        fn with_spaces() {
            assert_eq!(
                **unwrap_parser(optional(Spanned::new("(with space)"))),
                "with space",
            );
        }

        #[test]
        fn with_escaped() {
            assert_eq!(
                **unwrap_parser(optional(Spanned::new("(with \\{)"))),
                "with \\{",
            );
        }

        #[test]
        fn with_closing_brace() {
            assert_eq!(
                **unwrap_parser(optional(Spanned::new("(with })"))),
                "with }",
            );
        }

        #[test]
        fn with_emoji() {
            assert_eq!(**unwrap_parser(optional(Spanned::new("(🦀)"))), "🦀");
        }

        #[test]
        fn errors_on_empty() {
            let span = Spanned::new("");

            assert_eq!(
                optional(span),
                Err(Err::Error(Error::Other(span, ErrorKind::Tag))),
            );
        }

        #[test]
        fn fails_on_empty() {
            let err = optional(Spanned::new("()")).unwrap_err();

            match err {
                Err::Failure(Error::EmptyOptional(e)) => {
                    assert_eq!(*e, "()");
                }
                Err::Incomplete(_) | Err::Error(_) | Err::Failure(_) => {
                    panic!("wrong error: {err:?}")
                }
            }
        }

        #[test]
        fn fails_on_escaped_non_reserved() {
            let err = optional(Spanned::new("(\\r)")).unwrap_err();

            match err {
                Err::Failure(Error::EscapedNonReservedCharacter(e)) => {
                    assert_eq!(*e, "\\r");
                }
                Err::Incomplete(_) | Err::Error(_) | Err::Failure(_) => {
                    panic!("wrong error: {err:?}")
                }
            }
        }

        #[test]
        fn fails_on_nested() {
            for input in [
                "((nest))",
                "(before(nest))",
                "((nest)after)",
                "(bef(nest)aft)",
            ] {
                match optional(Spanned::new(input)).expect_err("error") {
                    Err::Failure(Error::NestedOptional(e)) => {
                        assert_eq!(*e, "(nest)", "on input: {input}");
                    }
                    e => panic!("wrong error: {e:?}"),
                }
            }
        }

        #[test]
        fn fails_on_parameter() {
            for input in [
                "({nest})",
                "(before{nest})",
                "({nest}after)",
                "(bef{nest}aft)",
            ] {
                match optional(Spanned::new(input)).expect_err("error") {
                    Err::Failure(Error::ParameterInOptional(e)) => {
                        assert_eq!(*e, "{nest}", "on input: {input}");
                    }
                    e => panic!("wrong error: {e:?}"),
                }
            }
        }

        #[test]
        fn fails_on_alternation() {
            for input in ["(/)", "(bef/)", "(/aft)", "(bef/aft)"] {
                match optional(Spanned::new(input)).expect_err("error") {
                    Err::Failure(Error::AlternationInOptional(e)) => {
                        assert_eq!(*e, "/", "on input: {input}");
                    }
                    e => panic!("wrong error: {e:?}"),
                }
            }
        }

        #[test]
        fn fails_on_unescaped_reserved_char() {
            for (input, expected) in
                [("({opt)", "{"), ("({n{e}st})", "{"), ("((nest)", "(")]
            {
                match optional(Spanned::new(input)).expect_err("error") {
                    Err::Failure(Error::UnescapedReservedCharacter(e)) => {
                        assert_eq!(*e, expected, "on input: {input}");
                    }
                    e => panic!("wrong error: {e:?}"),
                }
            }
        }

        #[test]
        fn fails_on_unfinished() {
            for input in ["(", "(name "] {
                match optional(Spanned::new(input)).expect_err("error") {
                    Err::Failure(Error::UnfinishedOptional(e)) => {
                        assert_eq!(*e, "(", "on input: {input}");
                    }
                    e => panic!("wrong error: {e:?}"),
                }
            }
        }
    }

    mod alternative {
        use super::{
            alternative, unwrap_parser, Alternative, Err, Error, ErrorKind,
            Spanned,
        };

        #[test]
        fn text() {
            for input in ["string", "🦀"] {
                match unwrap_parser(alternative(Spanned::new(input))) {
                    Alternative::Text(t) => {
                        assert_eq!(*t, input, "on input: {input}");
                    }
                    _ => panic!("expected Alternative::Text"),
                }
            }
        }

        #[test]
        fn escaped_spaces() {
            for input in ["bef\\ ", "\\ aft", "bef\\ aft"] {
                match unwrap_parser(alternative(Spanned::new(input))) {
                    Alternative::Text(t) => {
                        assert_eq!(*t, input, "on input: {input}");
                    }
                    _ => panic!("expected Alternative::Text"),
                }
            }
        }

        #[test]
        fn optional() {
            match unwrap_parser(alternative(Spanned::new("(opt)"))) {
                Alternative::Optional(t) => {
                    assert_eq!(**t, "opt");
                }
                Alternative::Text(_) => {
                    panic!("expected Alternative::Optional");
                }
            }
        }

        #[test]
        fn not_captures_unescaped_whitespace() {
            match alternative(Spanned::new("text ")) {
                Ok((rest, matched)) => {
                    assert_eq!(*rest, " ");

                    match matched {
                        Alternative::Text(t) => assert_eq!(*t, "text"),
                        Alternative::Optional(_) => {
                            panic!("expected Alternative::Text");
                        }
                    }
                }
                Err(..) => panic!("expected ok"),
            }
        }

        #[test]
        fn errors_on_empty() {
            match alternative(Spanned::new("")).unwrap_err() {
                Err::Error(Error::Other(_, ErrorKind::Alt)) => {}
                e @ (Err::Incomplete(_) | Err::Error(_) | Err::Failure(_)) => {
                    panic!("wrong error: {e:?}");
                }
            }
        }

        #[test]
        fn fails_on_unfinished_optional() {
            for input in ["(", "(opt"] {
                match alternative(Spanned::new(input)).unwrap_err() {
                    Err::Failure(Error::UnfinishedOptional(e)) => {
                        assert_eq!(*e, "(", "on input: {input}");
                    }
                    e => panic!("wrong error: {e:?}"),
                }
            }
        }

        #[test]
        fn fails_on_escaped_non_reserved() {
            for input in ["(\\r)", "\\r"] {
                match alternative(Spanned::new(input)).unwrap_err() {
                    Err::Failure(Error::EscapedNonReservedCharacter(e)) => {
                        assert_eq!(*e, "\\r", "on input: {input}");
                    }
                    e => panic!("wrong error: {e:?}"),
                }
            }
        }
    }

    mod alternation {
        use super::{
            alternation, assert_ast_eq, unwrap_parser, Err, Error, ErrorKind,
            Spanned,
        };

        #[test]
        fn basic() {
            assert_ast_eq(
                unwrap_parser(alternation(Spanned::new("l/🦀"))),
                r#"Alternation(
                    [
                        [
                            Text(
                                LocatedSpan {
                                    offset: 0,
                                    line: 1,
                                    fragment: "l",
                                    extra: (),
                                },
                            ),
                        ],
                        [
                            Text(
                                LocatedSpan {
                                    offset: 2,
                                    line: 1,
                                    fragment: "🦀",
                                    extra: (),
                                },
                            ),
                        ],
                    ],
                )"#,
            );
        }

        #[test]
        fn with_optionals() {
            assert_ast_eq(
                unwrap_parser(alternation(Spanned::new(
                    "l(opt)/(opt)r/l(opt)r",
                ))),
                r#"Alternation(
                    [
                        [
                            Text(
                                LocatedSpan {
                                    offset: 0,
                                    line: 1,
                                    fragment: "l",
                                    extra: (),
                                },
                            ),
                            Optional(
                                Optional(
                                    LocatedSpan {
                                        offset: 2,
                                        line: 1,
                                        fragment: "opt",
                                        extra: (),
                                    },
                                ),
                            ),
                        ],
                        [
                            Optional(
                                Optional(
                                    LocatedSpan {
                                        offset: 8,
                                        line: 1,
                                        fragment: "opt",
                                        extra: (),
                                    },
                                ),
                            ),
                            Text(
                                LocatedSpan {
                                    offset: 12,
                                    line: 1,
                                    fragment: "r",
                                    extra: (),
                                },
                            ),
                        ],
                        [
                            Text(
                                LocatedSpan {
                                    offset: 14,
                                    line: 1,
                                    fragment: "l",
                                    extra: (),
                                },
                            ),
                            Optional(
                                Optional(
                                    LocatedSpan {
                                        offset: 16,
                                        line: 1,
                                        fragment: "opt",
                                        extra: (),
                                    },
                                ),
                            ),
                            Text(
                                LocatedSpan {
                                    offset: 20,
                                    line: 1,
                                    fragment: "r",
                                    extra: (),
                                },
                            ),
                        ],
                    ],
                )"#,
            );
        }

        #[test]
        fn with_more_optionals() {
            assert_ast_eq(
                unwrap_parser(alternation(Spanned::new(
                    "l(opt)(opt)/(opt)(opt)r/(opt)m(opt)",
                ))),
                r#"Alternation(
                    [
                        [
                            Text(
                                LocatedSpan {
                                    offset: 0,
                                    line: 1,
                                    fragment: "l",
                                    extra: (),
                                },
                            ),
                            Optional(
                                Optional(
                                    LocatedSpan {
                                        offset: 2,
                                        line: 1,
                                        fragment: "opt",
                                        extra: (),
                                    },
                                ),
                            ),
                            Optional(
                                Optional(
                                    LocatedSpan {
                                        offset: 7,
                                        line: 1,
                                        fragment: "opt",
                                        extra: (),
                                    },
                                ),
                            ),
                        ],
                        [
                            Optional(
                                Optional(
                                    LocatedSpan {
                                        offset: 13,
                                        line: 1,
                                        fragment: "opt",
                                        extra: (),
                                    },
                                ),
                            ),
                            Optional(
                                Optional(
                                    LocatedSpan {
                                        offset: 18,
                                        line: 1,
                                        fragment: "opt",
                                        extra: (),
                                    },
                                ),
                            ),
                            Text(
                                LocatedSpan {
                                    offset: 22,
                                    line: 1,
                                    fragment: "r",
                                    extra: (),
                                },
                            ),
                        ],
                        [
                            Optional(
                                Optional(
                                    LocatedSpan {
                                        offset: 25,
                                        line: 1,
                                        fragment: "opt",
                                        extra: (),
                                    },
                                ),
                            ),
                            Text(
                                LocatedSpan {
                                    offset: 29,
                                    line: 1,
                                    fragment: "m",
                                    extra: (),
                                },
                            ),
                            Optional(
                                Optional(
                                    LocatedSpan {
                                        offset: 31,
                                        line: 1,
                                        fragment: "opt",
                                        extra: (),
                                    },
                                ),
                            ),
                        ],
                    ],
                )"#,
            );
        }

        #[test]
        fn errors_without_slash() {
            for (input, expected) in [
                ("", ErrorKind::Many1),
                ("{par}", ErrorKind::Many1),
                ("text", ErrorKind::Tag),
                ("(opt)", ErrorKind::Tag),
            ] {
                match alternation(Spanned::new(input)).unwrap_err() {
                    Err::Error(Error::Other(_, kind)) => {
                        assert_eq!(kind, expected, "on input: {input}");
                    }
                    e => panic!("wrong error: {e:?}"),
                }
            }
        }

        #[test]
        fn fails_on_empty_alternation() {
            for input in ["/", "l/", "/r", "l/m/", "l//r", "/m/r"] {
                match alternation(Spanned::new(input)).unwrap_err() {
                    Err::Failure(Error::EmptyAlternation(e)) => {
                        assert_eq!(*e, "/", "on input: {input}");
                    }
                    e => panic!("wrong error: {e:?}"),
                }
            }
        }

        #[test]
        fn fails_on_only_optional() {
            for input in
                ["text/(opt)", "text/(opt)(opt)", "(opt)/text", "(opt)/(opt)"]
            {
                match alternation(Spanned::new(input)).unwrap_err() {
                    Err::Failure(Error::OnlyOptionalInAlternation(e)) => {
                        assert_eq!(*e, input, "on input: {input}");
                    }
                    e => panic!("wrong error: {e:?}"),
                }
            }
        }
    }

    // All test examples from: <https://git.io/J159C>
    // Naming of test cases is preserved.
    mod expression {
        use super::{
            assert_ast_eq, expression, unwrap_parser, Err, Error, Spanned,
        };

        #[test]
        fn parameters_ids() {
            assert_ast_eq(
                unwrap_parser(expression(Spanned::new("{string} {string}"))),
                r#"Expression(
                    [
                        Parameter(
                            Parameter {
                                input: LocatedSpan {
                                    offset: 1,
                                    line: 1,
                                    fragment: "string",
                                    extra: (),
                                },
                                id: 0,
                            },
                        ),
                        Whitespaces(
                            LocatedSpan {
                                offset: 8,
                                line: 1,
                                fragment: " ",
                                extra: (),
                            },
                        ),
                        Parameter(
                            Parameter {
                                input: LocatedSpan {
                                    offset: 10,
                                    line: 1,
                                    fragment: "string",
                                    extra: (),
                                },
                                id: 1,
                            },
                        ),
                    ],
                )"#,
            )
        }

        #[test]
        fn allows_escaped_optional_parameter_types() {
            assert_ast_eq(
                unwrap_parser(expression(Spanned::new("\\({int})"))),
                r#"Expression(
                    [
                        Text(
                            LocatedSpan {
                                offset: 0,
                                line: 1,
                                fragment: "\\(",
                                extra: (),
                            },
                        ),
                        Parameter(
                            Parameter {
                                input: LocatedSpan {
                                    offset: 3,
                                    line: 1,
                                    fragment: "int",
                                    extra: (),
                                },
                                id: 0,
                            },
                        ),
                        Text(
                            LocatedSpan {
                                offset: 7,
                                line: 1,
                                fragment: ")",
                                extra: (),
                            },
                        ),
                    ],
                )"#,
            );
        }

        #[test]
        fn allows_parameter_type_in_alternation() {
            assert_ast_eq(
                unwrap_parser(expression(Spanned::new("a/i{int}n/y"))),
                r#"Expression(
                    [
                        Alternation(
                            Alternation(
                                [
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 0,
                                                line: 1,
                                                fragment: "a",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 2,
                                                line: 1,
                                                fragment: "i",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                ],
                            ),
                        ),
                        Parameter(
                            Parameter {
                                input: LocatedSpan {
                                    offset: 4,
                                    line: 1,
                                    fragment: "int",
                                    extra: (),
                                },
                                id: 0,
                            },
                        ),
                        Alternation(
                            Alternation(
                                [
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 8,
                                                line: 1,
                                                fragment: "n",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 10,
                                                line: 1,
                                                fragment: "y",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                ],
                            ),
                        ),
                    ],
                )"#,
            );
        }

        #[test]
        fn does_allow_parameter_adjacent_to_alternation() {
            assert_ast_eq(
                unwrap_parser(expression(Spanned::new("{int}st/nd/rd/th"))),
                r#"Expression(
                    [
                        Parameter(
                            Parameter {
                                input: LocatedSpan {
                                    offset: 1,
                                    line: 1,
                                    fragment: "int",
                                    extra: (),
                                },
                                id: 0,
                            },
                        ),
                        Alternation(
                            Alternation(
                                [
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 5,
                                                line: 1,
                                                fragment: "st",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 8,
                                                line: 1,
                                                fragment: "nd",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 11,
                                                line: 1,
                                                fragment: "rd",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 14,
                                                line: 1,
                                                fragment: "th",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                ],
                            ),
                        ),
                    ],
                )"#,
            );
        }

        #[test]
        fn does_not_allow_alternation_in_optional() {
            match expression(Spanned::new("three( brown/black) mice"))
                .unwrap_err()
            {
                Err::Failure(Error::AlternationInOptional(s)) => {
                    assert_eq!(*s, "/");
                }
                e @ (Err::Incomplete(_) | Err::Error(_) | Err::Failure(_)) => {
                    panic!("wrong error: {e:?}");
                }
            }
        }

        #[rustfmt::skip]
        #[test]
        fn does_not_allow_alternation_with_empty_alternative_by_adjacent_left_parameter(
        ) {
            match expression(Spanned::new("{int}/x")).unwrap_err() {
                Err::Failure(Error::EmptyAlternation(s)) => {
                    assert_eq!(*s, "/");
                }
                e @ (Err::Incomplete(_) | Err::Error(_) | Err::Failure(_)) => {
                    panic!("wrong error: {e:?}");
                }
            }
        }

        #[rustfmt::skip]
        #[test]
        fn does_not_allow_alternation_with_empty_alternative_by_adjacent_optional(
        ) {
            match expression(Spanned::new("three (brown)/black mice"))
                .unwrap_err()
            {
                Err::Failure(Error::OnlyOptionalInAlternation(s)) => {
                    assert_eq!(*s, "(brown)/black");
                }
                e @ (Err::Incomplete(_) | Err::Error(_) | Err::Failure(_)) => {
                    panic!("wrong error: {e:?}");
                }
            }
        }

        #[rustfmt::skip]
        #[test]
        fn does_not_allow_alternation_with_empty_alternative_by_adjacent_right_parameter(
        ) {
            match expression(Spanned::new("x/{int}")).unwrap_err() {
                Err::Failure(Error::EmptyAlternation(s)) => {
                    assert_eq!(*s, "/");
                }
                e @ (Err::Incomplete(_) | Err::Error(_) | Err::Failure(_)) => {
                    panic!("wrong error: {e:?}");
                }
            }
        }

        #[test]
        fn does_not_allow_alternation_with_empty_alternative() {
            match expression(Spanned::new("three brown//black mice"))
                .unwrap_err()
            {
                Err::Failure(Error::EmptyAlternation(s)) => {
                    assert_eq!(*s, "/");
                }
                e @ (Err::Incomplete(_) | Err::Error(_) | Err::Failure(_)) => {
                    panic!("wrong error: {e:?}");
                }
            }
        }

        #[test]
        fn does_not_allow_empty_optional() {
            match expression(Spanned::new("three () mice")).unwrap_err() {
                Err::Failure(Error::EmptyOptional(s)) => {
                    assert_eq!(*s, "()");
                }
                e @ (Err::Incomplete(_) | Err::Error(_) | Err::Failure(_)) => {
                    panic!("wrong error: {e:?}");
                }
            }
        }

        #[test]
        fn does_not_allow_nested_optional() {
            match expression(Spanned::new("(a(b))")).unwrap_err() {
                Err::Failure(Error::NestedOptional(s)) => {
                    assert_eq!(*s, "(b)");
                }
                e @ (Err::Incomplete(_) | Err::Error(_) | Err::Failure(_)) => {
                    panic!("wrong error: {e:?}");
                }
            }
        }

        #[test]
        fn does_not_allow_optional_parameter_types() {
            match expression(Spanned::new("({int})")).unwrap_err() {
                Err::Failure(Error::ParameterInOptional(s)) => {
                    assert_eq!(*s, "{int}");
                }
                e @ (Err::Incomplete(_) | Err::Error(_) | Err::Failure(_)) => {
                    panic!("wrong error: {e:?}");
                }
            }
        }

        #[test]
        fn does_not_allow_parameter_name_with_reserved_characters() {
            match expression(Spanned::new("{(string)}")).unwrap_err() {
                Err::Failure(Error::OptionalInParameter(s)) => {
                    assert_eq!(*s, "(string)");
                }
                e @ (Err::Incomplete(_) | Err::Error(_) | Err::Failure(_)) => {
                    panic!("wrong error: {e:?}");
                }
            }
        }

        #[test]
        fn does_not_allow_unfinished_parenthesis_1() {
            match expression(Spanned::new(
                "three (exceptionally\\) {string\\} mice",
            ))
            .unwrap_err()
            {
                Err::Failure(Error::UnescapedReservedCharacter(s)) => {
                    assert_eq!(*s, "{");
                }
                e @ (Err::Incomplete(_) | Err::Error(_) | Err::Failure(_)) => {
                    panic!("wrong error: {e:?}");
                }
            }
        }

        #[test]
        fn does_not_allow_unfinished_parenthesis_2() {
            match expression(Spanned::new(
                "three (exceptionally\\) {string} mice",
            ))
            .unwrap_err()
            {
                Err::Failure(Error::ParameterInOptional(s)) => {
                    assert_eq!(*s, "{string}");
                }
                e @ (Err::Incomplete(_) | Err::Error(_) | Err::Failure(_)) => {
                    panic!("wrong error: {e:?}");
                }
            }
        }

        #[test]
        fn does_not_allow_unfinished_parenthesis_3() {
            match expression(Spanned::new(
                "three ((exceptionally\\) strong) mice",
            ))
            .unwrap_err()
            {
                Err::Failure(Error::UnescapedReservedCharacter(s)) => {
                    assert_eq!(*s, "(");
                }
                e @ (Err::Incomplete(_) | Err::Error(_) | Err::Failure(_)) => {
                    panic!("wrong error: {e:?}");
                }
            }
        }

        #[test]
        fn matches_alternation() {
            assert_ast_eq(
                unwrap_parser(expression(Spanned::new(
                    "mice/rats and rats\\/mice",
                ))),
                r#"Expression(
                    [
                        Alternation(
                            Alternation(
                                [
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 0,
                                                line: 1,
                                                fragment: "mice",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 5,
                                                line: 1,
                                                fragment: "rats",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                ],
                            ),
                        ),
                        Whitespaces(
                            LocatedSpan {
                                offset: 9,
                                line: 1,
                                fragment: " ",
                                extra: (),
                            },
                        ),
                        Text(
                            LocatedSpan {
                                offset: 10,
                                line: 1,
                                fragment: "and",
                                extra: (),
                            },
                        ),
                        Whitespaces(
                            LocatedSpan {
                                offset: 13,
                                line: 1,
                                fragment: " ",
                                extra: (),
                            },
                        ),
                        Text(
                            LocatedSpan {
                                offset: 14,
                                line: 1,
                                fragment: "rats\\/mice",
                                extra: (),
                            },
                        ),
                    ],
                )"#,
            );
        }

        #[test]
        fn matches_anonymous_parameter_type() {
            assert_ast_eq(
                unwrap_parser(expression(Spanned::new("{}"))),
                r#"Expression(
                    [
                        Parameter(
                            Parameter {
                                input: LocatedSpan {
                                    offset: 1,
                                    line: 1,
                                    fragment: "",
                                    extra: (),
                                },
                                id: 0,
                            },
                        ),
                    ],
                )"#,
            );
        }

        #[test]
        fn matches_doubly_escaped_parenthesis() {
            assert_ast_eq(
                unwrap_parser(expression(Spanned::new(
                    "three \\(exceptionally) \\{string} mice",
                ))),
                r#"Expression(
                    [
                        Text(
                            LocatedSpan {
                                offset: 0,
                                line: 1,
                                fragment: "three",
                                extra: (),
                            },
                        ),
                        Whitespaces(
                            LocatedSpan {
                                offset: 5,
                                line: 1,
                                fragment: " ",
                                extra: (),
                            },
                        ),
                        Text(
                            LocatedSpan {
                                offset: 6,
                                line: 1,
                                fragment: "\\(exceptionally)",
                                extra: (),
                            },
                        ),
                        Whitespaces(
                            LocatedSpan {
                                offset: 22,
                                line: 1,
                                fragment: " ",
                                extra: (),
                            },
                        ),
                        Text(
                            LocatedSpan {
                                offset: 23,
                                line: 1,
                                fragment: "\\{string}",
                                extra: (),
                            },
                        ),
                        Whitespaces(
                            LocatedSpan {
                                offset: 32,
                                line: 1,
                                fragment: " ",
                                extra: (),
                            },
                        ),
                        Text(
                            LocatedSpan {
                                offset: 33,
                                line: 1,
                                fragment: "mice",
                                extra: (),
                            },
                        ),
                    ],
                )"#,
            );
        }

        #[test]
        fn matches_doubly_escaped_slash() {
            assert_ast_eq(
                unwrap_parser(expression(Spanned::new("12\\\\/2020"))),
                r#"Expression(
                    [
                        Alternation(
                            Alternation(
                                [
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 0,
                                                line: 1,
                                                fragment: "12\\\\",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 5,
                                                line: 1,
                                                fragment: "2020",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                ],
                            ),
                        ),
                    ],
                )"#,
            );
        }

        #[test]
        fn matches_optional_before_alternation() {
            assert_ast_eq(
                unwrap_parser(expression(Spanned::new(
                    "three (brown )mice/rats",
                ))),
                r#"Expression(
                    [
                        Text(
                            LocatedSpan {
                                offset: 0,
                                line: 1,
                                fragment: "three",
                                extra: (),
                            },
                        ),
                        Whitespaces(
                            LocatedSpan {
                                offset: 5,
                                line: 1,
                                fragment: " ",
                                extra: (),
                            },
                        ),
                        Alternation(
                            Alternation(
                                [
                                    [
                                        Optional(
                                            Optional(
                                                LocatedSpan {
                                                    offset: 7,
                                                    line: 1,
                                                    fragment: "brown ",
                                                    extra: (),
                                                },
                                            ),
                                        ),
                                        Text(
                                            LocatedSpan {
                                                offset: 14,
                                                line: 1,
                                                fragment: "mice",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 19,
                                                line: 1,
                                                fragment: "rats",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                ],
                            ),
                        ),
                    ],
                )"#,
            );
        }

        #[test]
        fn matches_optional_in_alternation() {
            assert_ast_eq(
                unwrap_parser(expression(Spanned::new(
                    "{int} rat(s)/mouse/mice",
                ))),
                r#"Expression(
                    [
                        Parameter(
                            Parameter {
                                input: LocatedSpan {
                                    offset: 1,
                                    line: 1,
                                    fragment: "int",
                                    extra: (),
                                },
                                id: 0,
                            },
                        ),
                        Whitespaces(
                            LocatedSpan {
                                offset: 5,
                                line: 1,
                                fragment: " ",
                                extra: (),
                            },
                        ),
                        Alternation(
                            Alternation(
                                [
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 6,
                                                line: 1,
                                                fragment: "rat",
                                                extra: (),
                                            },
                                        ),
                                        Optional(
                                            Optional(
                                                LocatedSpan {
                                                    offset: 10,
                                                    line: 1,
                                                    fragment: "s",
                                                    extra: (),
                                                },
                                            ),
                                        ),
                                    ],
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 13,
                                                line: 1,
                                                fragment: "mouse",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                    [
                                        Text(
                                            LocatedSpan {
                                                offset: 19,
                                                line: 1,
                                                fragment: "mice",
                                                extra: (),
                                            },
                                        ),
                                    ],
                                ],
                            ),
                        ),
                    ],
                )"#,
            );
        }

        #[test]
        fn err_on_escaped_end_of_line() {
            match expression(Spanned::new("\\")).unwrap_err() {
                Err::Failure(Error::EscapedEndOfLine(_)) => {}
                e @ (Err::Incomplete(_) | Err::Error(_) | Err::Failure(_)) => {
                    panic!("wrong err: {e}");
                }
            }
        }

        #[test]
        fn empty() {
            assert_ast_eq(
                unwrap_parser(expression(Spanned::new(""))),
                r#"Expression([],)"#,
            );
        }
    }
}
