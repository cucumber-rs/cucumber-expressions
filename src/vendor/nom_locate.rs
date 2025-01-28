use std::{
    hash::{Hash, Hasher},
    slice,
    str::FromStr,
};

use bytecount::{naive_num_chars, num_chars};
use derive_more::{Deref, Display};
use memchr::{memchr, Memchr};
use nom::{
    error::{ErrorKind, ParseError},
    AsBytes, Compare, CompareResult, Err, ExtendInto, FindSubstring, FindToken,
    IResult, Input, InputTakeAtPosition, Offset, ParseTo,
};

#[cfg(doc)]
use self as nom_locate;

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
    /// The column could be computed through the [`get_column()`] or
    /// [`get_utf8_column()`] methods.
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
    /// assert_eq!(span.get_column(), 1);
    /// assert_eq!(span.fragment(), &&b"foobar"[..]);
    /// ```
    ///
    /// [`get_column()`]: LocatedSpan::get_column
    /// [`get_utf8_column()`]: LocatedSpan::get_utf8_column
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
    /// The column could be computed through the [`get_column()`] or
    /// [`get_utf8_column()`] methods.
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
    /// assert_eq!(span.get_column(), 1);
    /// assert_eq!(span.fragment(), &&b"foobar"[..]);
    /// assert_eq!(span.extra, "extra");
    /// ```
    ///
    /// [`get_column()`]: LocatedSpan::get_column
    /// [`get_utf8_column()`]: LocatedSpan::get_utf8_column
    #[must_use]
    pub fn new_extra(program: T, extra: X) -> Self {
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
    pub fn location_offset(&self) -> usize {
        self.offset
    }

    /// Returns the line number of the fragment relatively to the input of the
    /// parser.
    ///
    /// It starts at line `1`.
    #[must_use]
    pub fn location_line(&self) -> u32 {
        self.line
    }

    /// Returns the fragment that is spanned, as a part of the input of the
    /// parser.
    #[must_use]
    pub fn fragment(&self) -> &T {
        &self.fragment
    }

    /// Returns the extra information embedded by the user (the parsed file
    /// name, for example).
    #[must_use]
    pub fn extra(&self) -> &X {
        &self.extra
    }
}

impl<T: AsBytes, X> LocatedSpan<T, X> {
    /// Attempts to get the "original" data slice back, by extending
    /// `self.fragment` backwards by the `self.offset`.
    ///
    /// > **NOTE**: Any bytes truncated from after `self.fragment` won't be
    /// >           recovered.
    fn get_unoffsetted_slice(&self) -> &[u8] {
        let self_bytes = self.fragment.as_bytes();
        let self_ptr = self_bytes.as_ptr();

        assert!(self.offset <= isize::MAX as usize, "offset is too big");

        unsafe {
            let orig_input_ptr = self_ptr.offset(-(self.offset as isize));
            slice::from_raw_parts(
                orig_input_ptr,
                self.offset + self_bytes.len(),
            )
        }
    }

    /// Attempts to get the "original" column and bytes back, by extending
    /// `self.fragment` backwards by the `self.offset`.
    fn get_columns_and_bytes_before(&self) -> (usize, &[u8]) {
        let before_self = &self.get_unoffsetted_slice()[..self.offset];

        let column = match memchr::memrchr(b'\n', before_self) {
            None => self.offset + 1,
            Some(pos) => self.offset - pos,
        };

        (column, &before_self[self.offset - (column - 1)..])
    }

    /// Returns the line that contains this [`LocatedSpan`].
    ///
    /// The [`get_column()`] and [`get_utf8_column()`] methods return indices
    /// that correspond to the line returned by this function.
    ///
    /// > **NOTE**: If this [`LocatedSpan`] ends before the end of the original
    /// >           data, the result of calling this method won't include any
    /// >           data from after this [`LocatedSpan`].
    ///
    /// ```rust
    /// # use cucumber_expressions::vendor::nom_locate::LocatedSpan;
    /// # use nom::{FindSubstring as _, Input as _};
    /// #
    /// let program = LocatedSpan::new(
    ///     "Hello World!\
    ///     \nThis is a multi-line input\
    ///     \nthat ends after this line.\n",
    /// );
    /// let multi = program.find_substring("multi").unwrap();
    ///
    /// assert_eq!(
    ///     program.slice(multi..).get_line_beginning(),
    ///     "This is a multi-line input".as_bytes(),
    /// );
    /// ```
    ///
    /// [`get_column()`]: LocatedSpan::get_column
    /// [`get_utf8_column()`]: LocatedSpan::get_utf8_column
    #[must_use]
    pub fn get_line_beginning(&self) -> &[u8] {
        let column0 = self.get_column() - 1;
        let the_line = &self.get_unoffsetted_slice()[self.offset - column0..];
        match memchr(b'\n', &the_line[column0..]) {
            None => the_line,
            Some(pos) => &the_line[..column0 + pos],
        }
    }

    /// Return the column index, assuming `1 byte = 1 column`.
    ///
    /// Use it for ASCII text, or use the [`get_utf8_column()`] for UTF-8.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use cucumber_expressions::vendor::nom_locate::LocatedSpan;
    /// # use nom::Input as _;
    /// #
    /// let span = LocatedSpan::new("foobar");
    ///
    /// assert_eq!(span.take_from(3).get_column(), 4);
    /// ```
    ///
    /// [`get_utf8_column()`]: LocatedSpan::get_utf8_column
    #[must_use]
    pub fn get_column(&self) -> usize {
        self.get_columns_and_bytes_before().0
    }

    /// Returns the column index for UTF-8 text.
    ///
    /// Returned value is unspecified for non-UTF-8 text.
    ///
    /// This version uses [`bytecount`]'s hyper algorithm to count characters.
    /// This is much faster for long lines, but is non-negligibly slower for
    /// short slices (below around 100 bytes). If you expect primarily short
    /// lines, you may get a noticeable speedup in parsing by using the
    /// [`naive_get_utf8_column()`] method instead. Benchmark your specific use
    /// case!
    ///
    /// # Example
    ///
    /// ```rust
    /// # use cucumber_expressions::vendor::nom_locate::LocatedSpan;
    /// # use nom::{FindSubstring as _, Input as _};
    /// #
    /// let span = LocatedSpan::new("メカジキ");
    /// let index_of_3rd_kanji = span.find_substring("ジ").unwrap();
    ///
    /// assert_eq!(span.take_from(index_of_3rd_kanji).get_column(), 7);
    /// assert_eq!(span.take_from(index_of_3rd_kanji).get_utf8_column(), 3);
    /// ```
    ///
    /// [`naive_get_utf8_column()`]: LocatedSpan::naive_get_utf8_column
    #[must_use]
    pub fn get_utf8_column(&self) -> usize {
        let before_self = self.get_columns_and_bytes_before().1;
        num_chars(before_self) + 1
    }

    /// Returns the column index for UTF-8 text.
    ///
    /// Returned value is unspecified for non-UTF-8 text.
    ///
    /// A simpler implementation of the [`get_utf8_column()`] method that may be
    /// faster on shorter lines. If benchmarking shows that this is faster, you
    /// can use it instead of [`get_utf8_column()`]. Prefer defaulting to
    /// [`get_utf8_column()`] unless this legitimately is a performance
    /// bottleneck.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use cucumber_expressions::vendor::nom_locate::LocatedSpan;
    /// # use nom::{FindSubstring as _, Input as _};
    /// #
    /// let span = LocatedSpan::new("メカジキ");
    /// let index_of_3rd_kanji = span.find_substring("ジ").unwrap();
    ///
    /// assert_eq!(span.take_from(index_of_3rd_kanji).get_column(), 7);
    /// assert_eq!(
    ///     span.take_from(index_of_3rd_kanji).naive_get_utf8_column(),
    ///     3,
    /// );
    /// ```
    ///
    /// [`get_utf8_column()`]: LocatedSpan::get_utf8_column
    #[must_use]
    pub fn naive_get_utf8_column(&self) -> usize {
        let before_self = self.get_columns_and_bytes_before().1;
        naive_num_chars(before_self) + 1
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
    T: Input + Offset,
    Self: Clone,
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

        let consumed = self.fragment.take(..consumed_len);

        let next_offset = self.offset + consumed_len;

        let consumed_as_bytes = consumed.as_bytes();
        let iter = Memchr::new(b'\n', consumed_as_bytes);
        let number_of_lines = iter.count() as u32;
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

        let consumed = self.fragment.take(..consumed_len);

        let next_offset = self.offset + consumed_len;

        let consumed_as_bytes = consumed.as_bytes();
        let iter = Memchr::new(b'\n', consumed_as_bytes);
        let number_of_lines = iter.count() as u32;
        let next_line = self.line + number_of_lines;

        Self {
            line: next_line,
            offset: next_offset,
            fragment: next_fragment,
            extra: self.extra.clone(),
        }
    }

    fn take_split(&self, index: usize) -> (Self, Self) {
        (self.take(index), self.take_from(index))
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
        self.fragment.extend_into(acc)
    }
}
