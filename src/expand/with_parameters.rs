// Copyright (c) 2021  Brendan Molloy <brendan@bbqsrc.net>,
//                     Ilya Solovyiov <ilya.solovyiov@gmail.com>,
//                     Kai Ren <tyranron@gmail.com>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! [Cucumber Expressions][1] [AST][2] with custom [`Parameter`]s into [`Regex`]
//! transformation definitions.
//!
//! [1]: https://github.com/cucumber/cucumber-expressions#readme
//! [2]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
//! [`Regex`]: regex::Regex

use std::{collections::HashMap, fmt::Display, iter, vec};

use either::Either;
use nom::{AsChar, InputIter};

use crate::{Parameter, SingleExpression};

use super::{
    Expression, IntoRegexCharIter, ParameterIter, SingleExpressionIter,
    UnknownParameterError,
};

/// Struct for pairing [Cucumber Expressions][1] [AST][2] `Item` with custom
/// `Parameters`.
///
/// Every [`Parameter`] should be represented by single [`Regex`] capturing
/// group.
///
/// [1]: https://github.com/cucumber/cucumber-expressions#readme
/// [2]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
/// [`Regex`]: regex::Regex
#[derive(Clone, Copy, Debug)]
pub struct WithParameters<Item, Parameters> {
    /// [Cucumber Expressions][1] [AST][2] `Item`.
    ///
    /// [1]: https://github.com/cucumber/cucumber-expressions#readme
    /// [2]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
    pub item: Item,

    /// Custom `Parameters`.
    pub parameters: Parameters,
}

/// Provider for custom [`Parameter`]s.
pub trait ParametersProvider<Input> {
    /// Returned value, that will be inserted into [`Regex`].
    ///
    /// Should be represented by single [`Regex`] capturing group.
    ///
    /// [`Regex`]: regex::Regex
    type Value;

    /// Returns [`Value`] corresponding to the `input`, if present.
    ///
    /// [`Value`]: Self::Value
    fn get(&self, input: &Input) -> Option<Self::Value>;
}

impl<'p, Input, Key, Value, S> ParametersProvider<Input>
    for &'p HashMap<Key, Value, S>
where
    Input: InputIter,
    <Input as InputIter>::Item: AsChar,
    Key: AsRef<str>,
    Value: AsRef<str>,
{
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

// false positive:
// TODO: remove once fixed: https://github.com/rust-lang/rust-clippy/issues/7360
#[allow(clippy::type_repetition_in_bounds)]
impl<Input, Pars> IntoRegexCharIter<Input>
    for WithParameters<Expression<Input>, Pars>
where
    Input: Clone + Display + InputIter,
    <Input as InputIter>::Item: AsChar,
    Pars: Clone + ParametersProvider<Input>,
    <Pars as ParametersProvider<Input>>::Value: InputIter,
    <<Pars as ParametersProvider<Input>>::Value as InputIter>::Item: AsChar,
{
    type Iter = ExpressionWithParsIter<Input, Pars>;

    fn into_regex_char_iter(self) -> Self::Iter {
        let add_pars: fn(_) -> _ =
            |(item, parameters)| WithParameters { item, parameters };
        let into_regex_char_iter: fn(_) -> _ =
            IntoRegexCharIter::into_regex_char_iter;
        iter::once(Ok('^'))
            .chain(
                self.item
                    .0
                    .into_iter()
                    .zip(iter::repeat(self.parameters))
                    .map(add_pars)
                    .flat_map(into_regex_char_iter),
            )
            .chain(iter::once(Ok('$')))
    }
}

/// [`IntoRegexCharIter::Iter`] for [`WithParameters`]`<`[`Expression`]`>`.
type ExpressionWithParsIter<I, P> = iter::Chain<
    iter::Chain<
        iter::Once<Result<char, UnknownParameterError<I>>>,
        iter::FlatMap<
            iter::Map<
                iter::Zip<vec::IntoIter<SingleExpression<I>>, iter::Repeat<P>>,
                fn(
                    (SingleExpression<I>, P),
                ) -> WithParameters<SingleExpression<I>, P>,
            >,
            SingleExprWithParsIter<I, P>,
            fn(
                WithParameters<SingleExpression<I>, P>,
            ) -> SingleExprWithParsIter<I, P>,
        >,
    >,
    iter::Once<Result<char, UnknownParameterError<I>>>,
>;

// false positive:
// TODO: remove once fixed: https://github.com/rust-lang/rust-clippy/issues/7360
#[allow(clippy::type_repetition_in_bounds)]
impl<Input, Pars> IntoRegexCharIter<Input>
    for WithParameters<SingleExpression<Input>, Pars>
where
    Input: Clone + Display + InputIter,
    <Input as InputIter>::Item: AsChar,
    Pars: ParametersProvider<Input>,
    <Pars as ParametersProvider<Input>>::Value: InputIter,
    <<Pars as ParametersProvider<Input>>::Value as InputIter>::Item: AsChar,
{
    type Iter = SingleExprWithParsIter<Input, Pars>;

    fn into_regex_char_iter(self) -> Self::Iter {
        use Either::{Left, Right};

        if let SingleExpression::Parameter(item) = self.item {
            Left(
                WithParameters {
                    item,
                    parameters: self.parameters,
                }
                .into_regex_char_iter(),
            )
        } else {
            Right(self.item.into_regex_char_iter())
        }
    }
}

/// [`IntoRegexCharIter::Iter`] for
/// [`WithParameters`]`<`[`SingleExpression`]`>`.
type SingleExprWithParsIter<I, P> = Either<
    <WithParameters<Parameter<I>, P> as IntoRegexCharIter<I>>::Iter,
    SingleExpressionIter<I>,
>;

// false positive:
// TODO: remove once fixed: https://github.com/rust-lang/rust-clippy/issues/7360
#[allow(clippy::type_repetition_in_bounds)]
impl<Input, P> IntoRegexCharIter<Input> for WithParameters<Parameter<Input>, P>
where
    Input: Clone + Display + InputIter,
    <Input as InputIter>::Item: AsChar,
    P: ParametersProvider<Input>,
    <P as ParametersProvider<Input>>::Value: InputIter,
    <<P as ParametersProvider<Input>>::Value as InputIter>::Item: AsChar,
{
    type Iter = WithParsIter<Input, P>;

    fn into_regex_char_iter(self) -> Self::Iter {
        use Either::{Left, Right};

        let ok: fn(_) -> _ = |c: <P::Value as InputIter>::Item| Ok(c.as_char());
        self.parameters.get(&self.item).map_or_else(
            || Right(self.item.into_regex_char_iter()),
            |v| {
                Left(
                    iter::once(Ok('('))
                        .chain(v.iter_elements().map(ok))
                        .chain(iter::once(Ok(')'))),
                )
            },
        )
    }
}

/// [`IntoRegexCharIter::Iter`] for [`WithParameters`]`<`[`Parameter`]`>`.
type WithParsIter<I, P> = Either<
    iter::Chain<
        iter::Chain<
            iter::Once<Result<char, UnknownParameterError<I>>>,
            iter::Map<
                <<P as ParametersProvider<I>>::Value as InputIter>::IterElem,
                fn(
                    <<P as ParametersProvider<I>>::Value as InputIter>::Item,
                ) -> Result<char, UnknownParameterError<I>>,
            >,
        >,
        iter::Once<Result<char, UnknownParameterError<I>>>,
    >,
    ParameterIter<I>,
>;

#[cfg(test)]
mod spec {
    use crate::Error;

    use super::{Expression, HashMap, UnknownParameterError};

    #[test]
    fn custom_parameter() {
        let pars = HashMap::from([("custom", "custom")]);

        assert_eq!(
            Expression::regex_with_parameters("{custom}", &pars)
                .unwrap_or_else(|e| panic!("failed: {}", e))
                .as_str(),
            "^(custom)$",
        );
    }

    #[test]
    fn default_parameter() {
        let pars = HashMap::from([("custom", "custom")]);

        assert_eq!(
            Expression::regex_with_parameters("{}", &pars)
                .unwrap_or_else(|e| panic!("failed: {}", e))
                .as_str(),
            "^(.*)$",
        );
    }

    #[test]
    fn unknown_parameter() {
        let pars = HashMap::<String, String>::new();

        match Expression::regex_with_parameters("{custom}", &pars).unwrap_err()
        {
            Error::Expansion(UnknownParameterError { not_found }) => {
                assert_eq!(*not_found, "custom");
            }
            e @ (Error::Regex(_) | Error::Parsing(_)) => {
                panic!("wrong err: {}", e)
            }
        }
    }
}
