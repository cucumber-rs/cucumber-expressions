//! Shrank version of `nom_locate` crate.

use std::{
    hash::{Hash, Hasher},
    str::FromStr,
};

use derive_more::{Deref, Display};
use memchr::Memchr;
use nom::{
    AsBytes, Compare, CompareResult, ExtendInto, FindSubstring, FindToken,
    Input, Offset, ParseTo,
};

#[cfg(doc)]
use super::nom_locate;

/// Set of meta information about the location of a token, including extra
/// information.
///
/// Can be used as an input of the [`nom`] parsers. It implements all the
/// necessary traits for [`LocatedSpan`]`<&str,X>` and
/// [`LocatedSpan`]`<&[u8],X>`.
#[derive(Clone, Copy, Debug, Deref, Display)]
#[display(fmt = "{}", fragment)]
pub struct LocatedSpan<T, X = ()> {
    /// Position of the fragment relatively to the input of the parser.
    ///
    /// It starts at offset `0`.
    offset: usize,

    /// Line number of the fragment relatively to the input of the parser.
    ///
    /// It starts at line `1`.
    line: u32,

    /// Fragment that is spanned, as a part of the input of the parser.
    #[deref]
    fragment: T,

    /// Extra information that can be embedded by the user (the parsed file
    /// name, for example).
    extra: X,
}

impl<T, U, X> AsRef<U> for LocatedSpan<&T, X>
where
    T: AsRef<U> + ?Sized,
    U: ?Sized,
{
    fn as_ref(&self) -> &U {
        self.fragment.as_ref()
    }
}

impl<T> LocatedSpan<T, ()> {
    /// Creates a new [`LocatedSpan`] for a particular input with default
    /// `offset`/`line` values and empty extra data.
    ///
    /// `offset` starts at `0`, `line` starts at `1`, and `column` starts at
    /// `1`.
    ///
    /// > **WARNING**: Do not use this constructor in parser functions. [`nom`]
    /// >              and [`nom_locate`] assume span offsets are relative to
    /// >              the beginning of the same input. In these cases, you
    /// >              probably want to use the [`nom::Input`] trait instead.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use cucumber_expressions::vendor::nom_locate::LocatedSpan;
    /// #
    /// let span = LocatedSpan::new(b"foobar");
    ///
    /// assert_eq!(span.location_offset(), 0);
    /// assert_eq!(span.location_line(), 1);
    /// assert_eq!(span.fragment(), &&b"foobar"[..]);
    #[must_use]
    pub const fn new(program: T) -> Self {
        Self {
            offset: 0,
            line: 1,
            fragment: program,
            extra: (),
        }
    }
}

impl<T, X> LocatedSpan<T, X> {
    /// Creates a new [`LocatedSpan`] for a particular input with default
    /// `offset` and `line` values and the provided `extra` information.
    ///
    /// `offset` starts at `0`, `line` starts at `1`, and `column` starts at
    /// `1`.
    ///
    /// > **WARNING**: Do not use this constructor in parser functions. [`nom`]
    /// >              and [`nom_locate`] assume span offsets are relative to
    /// >              the beginning of the same input. In these cases, you
    /// >              probably want to use the [`nom::Input`] trait instead.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use cucumber_expressions::vendor::nom_locate::LocatedSpan;
    /// #
    /// let span = LocatedSpan::new_extra(b"foobar", "extra");
    ///
    /// assert_eq!(span.location_offset(), 0);
    /// assert_eq!(span.location_line(), 1);
    /// assert_eq!(span.fragment(), &&b"foobar"[..]);
    /// assert_eq!(*span.extra(), "extra");
    /// ```
    #[must_use]
    pub const fn new_extra(program: T, extra: X) -> Self {
        Self {
            offset: 0,
            line: 1,
            fragment: program,
            extra,
        }
    }

    /// Returns the position of the fragment relatively to the input of the
    /// parser.
    ///
    /// It starts at offset `0`.
    #[must_use]
    pub const fn location_offset(&self) -> usize {
        self.offset
    }

    /// Returns the line number of the fragment relatively to the input of the
    /// parser.
    ///
    /// It starts at line `1`.
    #[must_use]
    pub const fn location_line(&self) -> u32 {
        self.line
    }

    /// Returns the fragment that is spanned, as a part of the input of the
    /// parser.
    #[must_use]
    pub const fn fragment(&self) -> &T {
        &self.fragment
    }

    /// Returns the extra information embedded by the user (the parsed file
    /// name, for example).
    #[must_use]
    pub const fn extra(&self) -> &X {
        &self.extra
    }
}

impl<T: Hash, X> Hash for LocatedSpan<T, X> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.offset.hash(state);
        self.line.hash(state);
        self.fragment.hash(state);
    }
}

impl<T: AsBytes, X: Default> From<T> for LocatedSpan<T, X> {
    fn from(i: T) -> Self {
        Self::new_extra(i, X::default())
    }
}

impl<T: AsBytes + PartialEq, X> PartialEq for LocatedSpan<T, X> {
    fn eq(&self, other: &Self) -> bool {
        self.line == other.line
            && self.offset == other.offset
            && self.fragment == other.fragment
    }
}

impl<T: AsBytes + Eq, X> Eq for LocatedSpan<T, X> {}

impl<T: AsBytes, X> AsBytes for LocatedSpan<T, X> {
    fn as_bytes(&self) -> &[u8] {
        self.fragment.as_bytes()
    }
}

impl<T, X> Input for LocatedSpan<T, X>
where
    T: AsBytes + Input + Offset,
    X: Clone,
{
    type Item = <T as Input>::Item;
    type Iter = <T as Input>::Iter;
    type IterIndices = <T as Input>::IterIndices;

    fn input_len(&self) -> usize {
        self.fragment.input_len()
    }

    fn take(&self, index: usize) -> Self {
        let next_fragment = self.fragment.take(index);
        let consumed_len = self.fragment.offset(&next_fragment);
        if consumed_len == 0 {
            return Self {
                line: self.line,
                offset: self.offset,
                fragment: next_fragment,
                extra: self.extra.clone(),
            };
        }

        let consumed = self.fragment.take(consumed_len);

        let next_offset = self.offset + consumed_len;

        let consumed_as_bytes = consumed.as_bytes();
        let iter = Memchr::new(b'\n', consumed_as_bytes);
        #[expect(clippy::unwrap_used, reason = "not happening")]
        let number_of_lines: u32 = iter.count().try_into().unwrap();
        let next_line = self.line + number_of_lines;

        Self {
            line: next_line,
            offset: next_offset,
            fragment: next_fragment,
            extra: self.extra.clone(),
        }
    }

    fn take_from(&self, index: usize) -> Self {
        let next_fragment = self.fragment.take_from(index);
        let consumed_len = self.fragment.offset(&next_fragment);
        if consumed_len == 0 {
            return Self {
                line: self.line,
                offset: self.offset,
                fragment: next_fragment,
                extra: self.extra.clone(),
            };
        }

        let consumed = self.fragment.take(consumed_len);

        let next_offset = self.offset + consumed_len;

        let consumed_as_bytes = consumed.as_bytes();
        let iter = Memchr::new(b'\n', consumed_as_bytes);
        #[expect(clippy::unwrap_used, reason = "not happening")]
        let number_of_lines: u32 = iter.count().try_into().unwrap();
        let next_line = self.line + number_of_lines;

        Self {
            line: next_line,
            offset: next_offset,
            fragment: next_fragment,
            extra: self.extra.clone(),
        }
    }

    fn take_split(&self, index: usize) -> (Self, Self) {
        (self.take_from(index), self.take(index))
    }

    fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool,
    {
        self.fragment.position(predicate)
    }

    fn iter_elements(&self) -> Self::Iter {
        self.fragment.iter_elements()
    }

    fn iter_indices(&self) -> Self::IterIndices {
        self.fragment.iter_indices()
    }

    fn slice_index(&self, count: usize) -> Result<usize, nom::Needed> {
        self.fragment.slice_index(count)
    }
}

impl<A: Compare<B>, B: Into<LocatedSpan<B>>, X> Compare<B>
    for LocatedSpan<A, X>
{
    fn compare(&self, t: B) -> CompareResult {
        self.fragment.compare(t.into().fragment)
    }

    fn compare_no_case(&self, t: B) -> CompareResult {
        self.fragment.compare_no_case(t.into().fragment)
    }
}

impl<Fragment: FindToken<Token>, Token, X> FindToken<Token>
    for LocatedSpan<Fragment, X>
{
    fn find_token(&self, token: Token) -> bool {
        self.fragment.find_token(token)
    }
}

impl<T, U, X> FindSubstring<U> for LocatedSpan<T, X>
where
    T: FindSubstring<U>,
{
    fn find_substring(&self, substr: U) -> Option<usize> {
        self.fragment.find_substring(substr)
    }
}

impl<R: FromStr, T: ParseTo<R>, X> ParseTo<R> for LocatedSpan<T, X> {
    fn parse_to(&self) -> Option<R> {
        self.fragment.parse_to()
    }
}

impl<T, X> Offset for LocatedSpan<T, X> {
    fn offset(&self, second: &Self) -> usize {
        let fst = self.offset;
        let snd = second.offset;

        snd - fst
    }
}

impl<T, X> ExtendInto for LocatedSpan<T, X>
where
    T: ExtendInto,
{
    type Item = T::Item;
    type Extender = T::Extender;

    fn new_builder(&self) -> Self::Extender {
        self.fragment.new_builder()
    }

    fn extend_into(&self, acc: &mut Self::Extender) {
        self.fragment.extend_into(acc);
    }
}
