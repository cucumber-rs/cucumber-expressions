// Copyright (c) 2021-2023  Brendan Molloy <brendan@bbqsrc.net>,
//                          Ilya Solovyiov <ilya.solovyiov@gmail.com>,
//                          Kai Ren <tyranron@gmail.com>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! [Cucumber Expressions][1] [AST].
//!
//! See details in the [grammar spec][0].
//!
//! [0]: crate#grammar
//! [1]: https://github.com/cucumber/cucumber-expressions#readme
//! [AST]: https://en.wikipedia.org/wiki/Abstract_syntax_tree

use derive_more::{AsRef, Deref, DerefMut};
use nom::{error::ErrorKind, Err, InputLength};
use nom_locate::LocatedSpan;

use crate::parse;

/// [`str`] along with its location information in the original input.
pub type Spanned<'s> = LocatedSpan<&'s str>;

/// Top-level `expression` defined in the [grammar spec][0].
///
/// See [`parse::expression()`] for the detailed grammar and examples.
///
/// [0]: crate#grammar
#[derive(AsRef, Clone, Debug, Deref, DerefMut, Eq, PartialEq)]
pub struct Expression<Input>(pub Vec<SingleExpression<Input>>);

impl<'s> TryFrom<&'s str> for Expression<Spanned<'s>> {
    type Error = parse::Error<Spanned<'s>>;

    fn try_from(value: &'s str) -> Result<Self, Self::Error> {
        parse::expression(Spanned::new(value))
            .map_err(|e| match e {
                Err::Error(e) | Err::Failure(e) => e,
                Err::Incomplete(n) => parse::Error::Needed(n),
            })
            .and_then(|(rest, parsed)| {
                rest.is_empty()
                    .then_some(parsed)
                    .ok_or(parse::Error::Other(rest, ErrorKind::Verify))
            })
    }
}

impl<'s> Expression<Spanned<'s>> {
    /// Parses the given `input` as an [`Expression`].
    ///
    /// # Errors
    ///
    /// See [`parse::Error`] for details.
    pub fn parse<I: AsRef<str> + ?Sized>(
        input: &'s I,
    ) -> Result<Self, parse::Error<Spanned<'s>>> {
        Self::try_from(input.as_ref())
    }
}

/// `single-expression` defined in the [grammar spec][0], representing a single
/// entry of an [`Expression`].
///
/// See [`parse::single_expression()`] for the detailed grammar and examples.
///
/// [0]: crate#grammar
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SingleExpression<Input> {
    /// [`alternation`][0] expression.
    ///
    /// [0]: crate#grammar
    Alternation(Alternation<Input>),

    /// [`optional`][0] expression.
    ///
    /// [0]: crate#grammar
    Optional(Optional<Input>),

    /// [`parameter`][0] expression.
    ///
    /// [0]: crate#grammar
    Parameter(Parameter<Input>),

    /// [`text-without-whitespace+`][0] expression.
    ///
    /// [0]: crate#grammar
    Text(Input),

    /// [`whitespace+`][0] expression.
    ///
    /// [0]: crate#grammar
    Whitespaces(Input),
}

/// `single-alternation` defined in the [grammar spec][0], representing a
/// building block of an [`Alternation`].
///
/// [0]: crate#grammar
pub type SingleAlternation<Input> = Vec<Alternative<Input>>;

/// `alternation` defined in the [grammar spec][0], allowing to match one of
/// [`SingleAlternation`]s.
///
/// See [`parse::alternation()`] for the detailed grammar and examples.
///
/// [0]: crate#grammar
#[derive(AsRef, Clone, Debug, Deref, DerefMut, Eq, PartialEq)]
pub struct Alternation<Input>(pub Vec<SingleAlternation<Input>>);

impl<Input: InputLength> Alternation<Input> {
    /// Returns length of this [`Alternation`]'s span in the `Input`.
    pub(crate) fn span_len(&self) -> usize {
        self.0
            .iter()
            .flatten()
            .map(|alt| match alt {
                Alternative::Text(t) => t.input_len(),
                Alternative::Optional(opt) => opt.input_len() + 2,
            })
            .sum::<usize>()
            + self.len()
            - 1
    }

    /// Indicates whether any of [`SingleAlternation`]s consists only from
    /// [`Optional`]s.
    pub(crate) fn contains_only_optional(&self) -> bool {
        (**self).iter().any(|single_alt| {
            single_alt
                .iter()
                .all(|alt| matches!(alt, Alternative::Optional(_)))
        })
    }
}

/// `alternative` defined in the [grammar spec][0].
///
/// See [`parse::alternative()`] for the detailed grammar and examples.
///
/// [0]: crate#grammar
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Alternative<Input> {
    /// [`optional`][1] expression.
    ///
    /// [1]: crate#grammar
    Optional(Optional<Input>),

    /// Text.
    Text(Input),
}

/// `optional` defined in the [grammar spec][0], allowing to match an optional
/// `Input`.
///
/// See [`parse::optional()`] for the detailed grammar and examples.
///
/// [0]: crate#grammar
#[derive(AsRef, Clone, Copy, Debug, Deref, DerefMut, Eq, PartialEq)]
pub struct Optional<Input>(pub Input);

/// `parameter` defined in the [grammar spec][0], allowing to match some special
/// `Input` described by a [`Parameter`] name.
///
/// See [`parse::parameter()`] for the detailed grammar and examples.
///
/// [0]: crate#grammar
#[derive(AsRef, Clone, Copy, Debug, Deref, DerefMut, Eq, PartialEq)]
pub struct Parameter<Input> {
    /// Inner `Input`.
    #[deref]
    #[deref_mut]
    pub input: Input,

    /// Unique ID of this [`Parameter`] in the parsed [`Expression`].
    #[as_ref(ignore)]
    pub id: usize,
}
