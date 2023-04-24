// Copyright (c) 2021-2023  Brendan Molloy <brendan@bbqsrc.net>,
//                          Ilya Solovyiov <ilya.solovyiov@gmail.com>,
//                          Kai Ren <tyranron@gmail.com>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Support for [custom][1] [`Parameter`]s.
//!
//! [1]: https://github.com/cucumber/cucumber-expressions#custom-parameter-types

use std::{collections::HashMap, fmt::Display, iter, str, vec};

use either::Either;
use nom::{AsChar, InputIter};

use crate::{expand::OwnedChars, Parameter, SingleExpression};

use super::{
    Expression, IntoRegexCharIter, ParameterError, ParameterIter,
    SingleExpressionIter,
};

/// Parser of a [Cucumber Expressions][0] [AST] `Element` with [custom][1]
/// `Parameters` in mind.
///
/// Usually, a [`Parameter`] is represented by a single [`Regex`] capturing
/// group. In case there are multiple capturing groups, they will be named like
/// `__{parameter_id}_{group_id}`. This is done to identify multiple capturing
/// groups related to a single [`Parameter`].
///
/// [`Regex`]: regex::Regex
/// [0]: https://github.com/cucumber/cucumber-expressions#readme
/// [1]: https://github.com/cucumber/cucumber-expressions#custom-parameter-types
/// [AST]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
#[derive(Clone, Copy, Debug)]
pub struct WithCustom<Element, Parameters> {
    /// Parsed element of a [Cucumber Expressions][0] [AST].
    ///
    /// [0]: https://github.com/cucumber/cucumber-expressions#readme
    /// [AST]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
    pub element: Element,

    /// Custom `Parameters` (in addition to [default ones][1]) to be used for
    /// expanding the `Element` into a [`Regex`].
    ///
    /// [`Regex`]: regex::Regex
    /// [1]: https://github.com/cucumber/cucumber-expressions#parameter-types
    pub parameters: Parameters,
}

/// Provider of custom [`Parameter`]s.
pub trait Provider<Input> {
    /// `<`[`Value`]` as `[`InputIter`]`>::`[`Item`].
    ///
    /// [`Item`]: InputIter::Item
    /// [`Value`]: Self::Value
    type Item: AsChar;

    /// Value matcher to be used in a [`Regex`].
    ///
    /// Usually, a [`Parameter`] is represented by a single [`Regex`] capturing
    /// group. In case there are multiple capturing groups, they will be named
    /// like `__{parameter_id}_{group_id}`. This is done to identify multiple
    /// capturing groups related to a single [`Parameter`].
    ///
    /// [`Regex`]: regex::Regex
    type Value: InputIter<Item = Self::Item>;

    /// Returns a [`Value`] matcher corresponding to the given `input`, if any.
    ///
    /// [`Value`]: Self::Value
    fn get(&self, input: &Input) -> Option<Self::Value>;
}

impl<'p, Input, Key, Value, S> Provider<Input> for &'p HashMap<Key, Value, S>
where
    Input: InputIter,
    <Input as InputIter>::Item: AsChar,
    Key: AsRef<str>,
    Value: AsRef<str>,
{
    type Item = char;
    type Value = &'p str;

    fn get(&self, input: &Input) -> Option<Self::Value> {
        self.iter().find_map(|(k, v)| {
            k.as_ref()
                .chars()
                .eq(input.iter_elements().map(AsChar::as_char))
                .then(|| v.as_ref())
        })
    }
}

impl<Input, Pars> IntoRegexCharIter<Input>
    for WithCustom<Expression<Input>, Pars>
where
    Input: Clone + Display + InputIter,
    <Input as InputIter>::Item: AsChar,
    Pars: Clone + Provider<Input>,
    <Pars as Provider<Input>>::Value: InputIter,
{
    type Iter = ExpressionWithParsIter<Input, Pars>;

    fn into_regex_char_iter(self) -> Self::Iter {
        let add_pars: fn(_) -> _ = |(item, parameters)| WithCustom {
            element: item,
            parameters,
        };
        let into_regex_char_iter: fn(_) -> _ =
            IntoRegexCharIter::into_regex_char_iter;
        iter::once(Ok('^'))
            .chain(
                self.element
                    .0
                    .into_iter()
                    .zip(iter::repeat(self.parameters))
                    .map(add_pars)
                    .flat_map(into_regex_char_iter),
            )
            .chain(iter::once(Ok('$')))
    }
}

// TODO: Replace with TAIT, once stabilized:
//       https://github.com/rust-lang/rust/issues/63063
/// [`IntoRegexCharIter::Iter`] for [`WithCustom`]`<`[`Expression`]`>`.
type ExpressionWithParsIter<I, P> = iter::Chain<
    iter::Chain<
        iter::Once<Result<char, ParameterError<I>>>,
        iter::FlatMap<
            iter::Map<
                iter::Zip<vec::IntoIter<SingleExpression<I>>, iter::Repeat<P>>,
                fn(
                    (SingleExpression<I>, P),
                ) -> WithCustom<SingleExpression<I>, P>,
            >,
            SingleExprWithParsIter<I, P>,
            fn(
                WithCustom<SingleExpression<I>, P>,
            ) -> SingleExprWithParsIter<I, P>,
        >,
    >,
    iter::Once<Result<char, ParameterError<I>>>,
>;

impl<Input, Pars> IntoRegexCharIter<Input>
    for WithCustom<SingleExpression<Input>, Pars>
where
    Input: Clone + Display + InputIter,
    <Input as InputIter>::Item: AsChar,
    Pars: Provider<Input>,
    <Pars as Provider<Input>>::Value: InputIter,
{
    type Iter = SingleExprWithParsIter<Input, Pars>;

    fn into_regex_char_iter(self) -> Self::Iter {
        use Either::{Left, Right};

        if let SingleExpression::Parameter(item) = self.element {
            Left(
                WithCustom {
                    element: item,
                    parameters: self.parameters,
                }
                .into_regex_char_iter(),
            )
        } else {
            Right(self.element.into_regex_char_iter())
        }
    }
}

// TODO: Replace with TAIT, once stabilized:
//       https://github.com/rust-lang/rust/issues/63063
/// [`IntoRegexCharIter::Iter`] for
/// [`WithCustom`]`<`[`SingleExpression`]`>`.
type SingleExprWithParsIter<I, P> = Either<
    <WithCustom<Parameter<I>, P> as IntoRegexCharIter<I>>::Iter,
    SingleExpressionIter<I>,
>;

impl<Input, P> IntoRegexCharIter<Input> for WithCustom<Parameter<Input>, P>
where
    Input: Clone + Display + InputIter,
    <Input as InputIter>::Item: AsChar,
    P: Provider<Input>,
    <P as Provider<Input>>::Value: InputIter,
{
    type Iter = WithParsIter<Input, P>;

    fn into_regex_char_iter(self) -> Self::Iter {
        use Either::{Left, Right};

        let id = self.element.id;

        match self.parameters.get(&self.element) {
            None => Right(Left(self.element.into_regex_char_iter())),
            Some(v) => {
                // We try to find '(' inside regex. If unsuccessfully, we can be
                // sure that the regex has no groups, so we can skip parsing.
                let parsed = v
                    .iter_elements()
                    .any(|c| c.as_char() == '(')
                    .then(|| {
                        let re = v
                            .iter_elements()
                            .map(AsChar::as_char)
                            .collect::<String>();
                        let hir = regex_syntax::Parser::new()
                            .parse(&re)
                            .map_err(|err| (self.element.input, re, err))?;
                        Ok(regex_hir::has_capture_groups(&hir).then_some(hir))
                    })
                    .transpose();
                let parsed = match parsed {
                    Ok(hir) => hir.flatten(),
                    Err((parameter, re, err)) => {
                        return Left(iter::once(Err(
                            ParameterError::RenameRegexGroup {
                                parameter,
                                re,
                                err: Box::new(err),
                            },
                        )));
                    }
                };

                parsed.map_or_else(
                    || {
                        let ok: fn(_) -> _ =
                            |c: <P::Value as InputIter>::Item| Ok(c.as_char());
                        Right(Right(Right(
                            iter::once(Ok('('))
                                .chain(v.iter_elements().map(ok))
                                .chain(iter::once(Ok(')'))),
                        )))
                    },
                    |cur_hir| {
                        let ok: fn(_) -> _ = Ok;
                        let new_hir =
                            regex_hir::rename_capture_groups(cur_hir, id);
                        Right(Right(Left(
                            "(?:"
                                .chars()
                                .map(ok)
                                .chain(
                                    OwnedChars::new(new_hir.to_string())
                                        .map(ok),
                                )
                                .chain(iter::once(Ok(')'))),
                        )))
                    },
                )
            }
        }
    }
}

// TODO: Replace with TAIT, once stabilized:
//       https://github.com/rust-lang/rust/issues/63063
/// [`IntoRegexCharIter::Iter`] for [`WithCustom`]`<`[`Parameter`]`>`.
type WithParsIter<I, P> = Either<
    iter::Once<Result<char, ParameterError<I>>>,
    Either<
        ParameterIter<I>,
        Either<
            iter::Chain<
                iter::Chain<
                    iter::Map<
                        str::Chars<'static>,
                        fn(char) -> Result<char, ParameterError<I>>,
                    >,
                    iter::Map<
                        OwnedChars,
                        fn(char) -> Result<char, ParameterError<I>>,
                    >,
                >,
                iter::Once<Result<char, ParameterError<I>>>,
            >,
            iter::Chain<
                iter::Chain<
                    iter::Once<Result<char, ParameterError<I>>>,
                    iter::Map<
                        <<P as Provider<I>>::Value as InputIter>::IterElem,
                        fn(
                            <<P as Provider<I>>::Value as InputIter>::Item,
                        )
                            -> Result<char, ParameterError<I>>,
                    >,
                >,
                iter::Once<Result<char, ParameterError<I>>>,
            >,
        >,
    >,
>;

/// Helpers to work with [`Regex`]es [`Hir`].
///
/// [`Hir`]: regex_syntax::hir::Hir
/// [`Regex`]: regex::Regex
mod regex_hir {
    use std::mem;

    use regex_syntax::hir::{Hir, HirKind};

    /// Checks whether the given [`Regex`] [`Hir`] contains any capturing
    /// groups.
    ///
    /// [`Regex`]: regex::Regex
    pub(super) fn has_capture_groups(hir: &Hir) -> bool {
        match hir.kind() {
            HirKind::Empty
            | HirKind::Literal(_)
            | HirKind::Class(_)
            | HirKind::Look(_)
            | HirKind::Repetition(_) => false,
            HirKind::Capture(_) => true,
            HirKind::Concat(inner) | HirKind::Alternation(inner) => {
                inner.iter().any(has_capture_groups)
            }
        }
    }

    /// Renames capturing groups in the given [`Hir`] via
    /// `__{parameter_id}_{group_id}` naming scheme.
    pub(super) fn rename_capture_groups(hir: Hir, parameter_id: usize) -> Hir {
        rename_groups_inner(hir, parameter_id, &mut 0)
    }

    /// Renames capturing groups in the given [`Hir`] via
    /// `__{parameter_id}_{group_id}` naming scheme, using the provided
    /// `group_id_indexer`.
    fn rename_groups_inner(
        hir: Hir,
        parameter_id: usize,
        group_id_indexer: &mut usize,
    ) -> Hir {
        match hir.into_kind() {
            HirKind::Empty => Hir::empty(),
            HirKind::Literal(lit) => Hir::literal(lit.0),
            HirKind::Class(cl) => Hir::class(cl),
            HirKind::Look(l) => Hir::look(l),
            HirKind::Repetition(rep) => Hir::repetition(rep),
            HirKind::Capture(mut capture) => {
                capture.name = Some(
                    format!("__{parameter_id}_{}", *group_id_indexer).into(),
                );
                *group_id_indexer += 1;

                let inner_hir =
                    mem::replace(capture.sub.as_mut(), Hir::empty());
                drop(mem::replace(
                    capture.sub.as_mut(),
                    rename_groups_inner(
                        inner_hir,
                        parameter_id,
                        group_id_indexer,
                    ),
                ));

                Hir::capture(capture)
            }
            HirKind::Concat(concat) => Hir::concat(
                concat
                    .into_iter()
                    .map(|h| {
                        rename_groups_inner(h, parameter_id, group_id_indexer)
                    })
                    .collect(),
            ),
            HirKind::Alternation(alt) => Hir::alternation(
                alt.into_iter()
                    .map(|h| {
                        rename_groups_inner(h, parameter_id, group_id_indexer)
                    })
                    .collect(),
            ),
        }
    }
}

#[cfg(test)]
mod spec {
    use crate::expand::Error;

    use super::{Expression, HashMap, ParameterError};

    #[test]
    fn custom_parameter() {
        let pars = HashMap::from([("custom", "custom")]);
        let expr = Expression::regex_with_parameters("{custom}", &pars)
            .unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(expr.as_str(), "^(custom)$");
    }

    #[test]
    fn custom_parameter_with_groups() {
        let pars = HashMap::from([("custom", "\"(custom)\"|'(custom)'")]);
        let expr =
            Expression::regex_with_parameters("{custom} {custom}", &pars)
                .unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(
            expr.as_str(),
            "^(?:(?:(?:\"(?P<__0_0>(?:custom))\")\
                    |(?:'(?P<__0_1>(?:custom))'))) \
              (?:(?:(?:\"(?P<__1_0>(?:custom))\")\
                    |(?:'(?P<__1_1>(?:custom))')))$",
        );
    }

    #[test]
    fn default_parameter() {
        let pars = HashMap::from([("custom", "custom")]);
        let expr = Expression::regex_with_parameters("{}", &pars)
            .unwrap_or_else(|e| panic!("failed: {e}"));

        assert_eq!(expr.as_str(), "^(.*)$");
    }

    #[test]
    fn unknown_parameter() {
        let pars = HashMap::<String, String>::new();

        match Expression::regex_with_parameters("{custom}", &pars).unwrap_err()
        {
            Error::Expansion(ParameterError::NotFound(not_found)) => {
                assert_eq!(*not_found, "custom");
            }
            e @ (Error::Regex(_) | Error::Parsing(_) | Error::Expansion(_)) => {
                panic!("wrong err: {e}")
            }
        }
    }
}
