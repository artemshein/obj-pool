use std::hash::Hash;

/// Type with a specific value we could reuse as `None` in `OptionInvalidValue`;
pub trait InvalidValue<T> {
    fn invalid_value() -> T;
}

/// Optimization for `Option<T>` where `T` implements an `InvalidValue` trait and reuses on of the
/// possible values of `T` to represents `None`. It's basically the same as `NonZero*`-types but more
/// powerful as it allows to reuse any value, not just `0` for any type, not just integers.
/// As a downside, it's not an `Option`, it's a separate type which is needed to be handled
/// explicitly.
///
/// ```
/// use obj_pool::invalid_value::{InvalidValue, OptionInvalidValue};
///
/// #[derive(PartialEq, Eq, Hash, Copy, Clone)]
/// struct A(u32);
///
/// impl InvalidValue<A> for A {
///   fn invalid_value() -> A {
///      A(155) // invalid value in our case
///   }
/// }
///
/// let mut v: OptionInvalidValue<A> = A(100).into();
/// assert!(v.is_some());
///
/// v = A(155).into();
/// assert!(v.is_none());
///
/// ```
#[derive(PartialEq, Debug, Copy, Clone, Eq, Hash)]
pub struct OptionInvalidValue<T: InvalidValue<T> + PartialEq + Copy + Eq + Hash>(T);

impl<T: InvalidValue<T> + PartialEq + Copy + Eq + Hash> OptionInvalidValue<T> {

    /// Make a `None` value
    pub fn none() -> OptionInvalidValue<T> {
        OptionInvalidValue(T::invalid_value())
    }

    /// Make an `Option<&T>`
    pub fn option(&self) -> Option<&T> {
        if self.is_some() {
            Some(&self.0)
        } else {
            None
        }
    }

    /// Get reference to underlying T, panics it it's `None`.
    pub fn as_ref_unchecked(&self) -> &T {
        if self.is_some() {
            &self.0
        } else {
            panic!("is none")
        }
    }

    /// Get mutable reference to underlying T, panics it it's `None`.
    pub fn as_ref_mut_unchecked(&mut self) -> &mut T {
        if self.is_some() {
            &mut self.0
        } else {
            panic!("is none")
        }
    }

    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Option<U> {
        Into::<Option<T>>::into(self).map(f)
    }
}

impl<T: InvalidValue<T> + PartialEq + Copy + Eq + Hash> IntoIterator for OptionInvalidValue<T> {
    type Item = T;
    type IntoIter = ::std::option::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        Into::<Option<T>>::into(self).into_iter()
    }
}

impl<T: InvalidValue<T> + PartialEq + Copy + Eq + Hash> From<Option<T>> for OptionInvalidValue<T> {
    fn from(v: Option<T>) -> Self {
        match v {
            Some(v) => OptionInvalidValue(v),
            _ => OptionInvalidValue::none(),
        }
    }
}

impl<T: InvalidValue<T> + PartialEq + Copy + Eq + Hash> Into<Option<T>> for OptionInvalidValue<T> {
    fn into(self) -> Option<T> {
        let val = self.0;
        if val == T::invalid_value() {
            None
        } else {
            Some(val)
        }
    }
}

/// Wraps a value in `OptionInvalidValue`, treats `T::invalid_value` as `None`
impl<T: InvalidValue<T> + PartialEq + Copy + Eq + Hash> From<T> for OptionInvalidValue<T> {
    fn from(v: T) -> Self {
        OptionInvalidValue(v)
    }
}

impl<T: InvalidValue<T> + PartialEq + Copy + Eq + Hash> OptionInvalidValue<T> {
    /// Checks if `OptionInvalidValue` is `Some`
    pub fn is_some(&self) -> bool {
        self.0 != T::invalid_value()
    }

    /// Checks if `OptionInvalidValue` is `None`
    pub fn is_none(&self) -> bool {
        !self.is_some()
    }

    /// Unwraps the `OptionInvalidValue`, panics in case of `None`.
    pub fn unwrap(self) -> T {
        if self.is_none() {
            panic!("unwrap on None");
        }
        self.0
    }
}