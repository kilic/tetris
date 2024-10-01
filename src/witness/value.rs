use crate::Error;
use std::ops::{Add, Mul, Neg, Sub};

// taken from pse/halo2

#[derive(Clone, Copy, Debug)]
pub struct Value<V> {
    inner: Option<V>,
}

impl<V> Default for Value<V> {
    fn default() -> Self {
        Self::empty()
    }
}

impl<T> From<T> for Value<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T: Clone> From<&T> for Value<T> {
    fn from(value: &T) -> Self {
        Self::new(value.clone())
    }
}

impl<T> From<Option<T>> for Value<T> {
    fn from(value: Option<T>) -> Self {
        Self { inner: value }
    }
}

#[cfg(feature = "halo2")]
impl<T> From<halo2_proofs::circuit::Value<T>> for Value<T> {
    fn from(external: halo2_proofs::circuit::Value<T>) -> Self {
        let mut this = Self::empty();
        external.map(|e| this.force(e));
        this
    }
}

impl<V> Value<Result<V, Error>> {
    pub fn ok(&self) -> Result<Value<V>, Error>
    where
        V: Clone,
    {
        match self.inner.clone() {
            Some(Ok(value)) => Ok(Value::new(value)),
            Some(Err(e)) => Err(e),
            None => Ok(Value::empty()),
        }
    }
}

impl<V> Value<V> {
    pub const fn empty() -> Self {
        Self { inner: None }
    }

    pub const fn new(value: V) -> Self {
        Self { inner: Some(value) }
    }

    #[allow(dead_code)]
    pub(crate) fn force(&mut self, value: V) {
        self.inner = Some(value);
    }

    pub fn as_ref(&self) -> Value<&V> {
        Value {
            inner: self.inner.as_ref(),
        }
    }

    pub fn as_mut(&mut self) -> Value<&mut V> {
        Value {
            inner: self.inner.as_mut(),
        }
    }

    pub fn and_then<W, F: FnOnce(V) -> Value<W>>(self, f: F) -> Value<W> {
        match self.inner {
            Some(v) => f(v),
            None => Value::empty(),
        }
    }

    pub fn map<W, F: FnOnce(V) -> W>(self, f: F) -> Value<W> {
        Value {
            inner: self.inner.map(f),
        }
    }

    pub fn zip<W>(self, other: Value<W>) -> Value<(V, W)> {
        Value {
            inner: self.inner.zip(other.inner),
        }
    }

    pub fn maybe<W, F: FnOnce(&V) -> Option<W>>(&self, f: F) -> Result<Value<W>, Error> {
        match self.inner.as_ref() {
            Some(value) => f(value).map(Value::new).ok_or(Error::Prover),
            None => Ok(Value::empty()),
        }
    }

    pub fn validate<F: FnOnce(&V) -> Result<(), Error>>(&self, f: F) -> Result<(), Error> {
        match self.inner.as_ref() {
            Some(value) => f(value),
            None => Ok(()),
        }
    }

    #[cfg(feature = "halo2")]
    pub fn halo2(&self) -> halo2_proofs::circuit::Value<V>
    where
        V: Copy,
    {
        self.inner
            .map(halo2_proofs::circuit::Value::known)
            .unwrap_or_else(halo2_proofs::circuit::Value::unknown)
    }
}

impl<V, W> Value<(V, W)> {
    pub fn unzip(self) -> (Value<V>, Value<W>) {
        match self.inner {
            Some((a, b)) => (Value::new(a), Value::new(b)),
            None => (Value::empty(), Value::empty()),
        }
    }
}

impl<V> Value<&V> {
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn copied(self) -> Value<V>
    where
        V: Copy,
    {
        Value {
            inner: self.inner.copied(),
        }
    }

    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn cloned(self) -> Value<V>
    where
        V: Clone,
    {
        Value {
            inner: self.inner.cloned(),
        }
    }
}

impl<V> Value<&mut V> {
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn copied(self) -> Value<V>
    where
        V: Copy,
    {
        Value {
            inner: self.inner.copied(),
        }
    }

    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn cloned(self) -> Value<V>
    where
        V: Clone,
    {
        Value {
            inner: self.inner.cloned(),
        }
    }
}

impl<V: Copy, const LEN: usize> Value<[V; LEN]> {
    pub fn transpose_array(self) -> [Value<V>; LEN] {
        let mut ret = [Value::empty(); LEN];
        if let Some(arr) = self.inner {
            for (entry, value) in ret.iter_mut().zip(arr) {
                *entry = Value::new(value);
            }
        }
        ret
    }
}

impl<V, I> Value<I>
where
    I: IntoIterator<Item = V>,
    I::IntoIter: ExactSizeIterator,
{
    pub fn transpose_vec(self, length: usize) -> Vec<Value<V>> {
        match self.inner {
            Some(values) => {
                let values = values.into_iter();
                assert_eq!(values.len(), length);
                values.map(Value::new).collect()
            }
            None => (0..length).map(|_| Value::empty()).collect(),
        }
    }
}

impl<V> Value<V> {
    pub fn map_transpose<W, F: FnOnce(V) -> I, I>(self, f: F, length: usize) -> Vec<Value<W>>
    where
        I: IntoIterator<Item = W>,
        I::IntoIter: ExactSizeIterator,
    {
        let vs = self.map(f);
        vs.transpose_vec(length)
    }
}

impl<V> Value<V> {
    pub fn map_transpose2<'a, W: 'a, F: FnOnce(&V) -> I, I>(
        &self,
        f: F,
        length: usize,
    ) -> Vec<Value<W>>
    where
        I: IntoIterator<Item = W>,
        I::IntoIter: ExactSizeIterator,
    {
        let vs = self.as_ref().map(f);
        vs.transpose_vec(length)
    }
}

impl<A, V: FromIterator<A>> FromIterator<Value<A>> for Value<V> {
    fn from_iter<I: IntoIterator<Item = Value<A>>>(iter: I) -> Self {
        Self {
            inner: iter.into_iter().map(|v| v.inner).collect(),
        }
    }
}

impl<V: Neg> Neg for Value<V> {
    type Output = Value<V::Output>;

    fn neg(self) -> Self::Output {
        Value {
            inner: self.inner.map(|v| -v),
        }
    }
}

impl<V, O> Add for Value<V>
where
    V: Add<Output = O>,
{
    type Output = Value<O>;

    fn add(self, rhs: Self) -> Self::Output {
        Value {
            inner: self.inner.zip(rhs.inner).map(|(a, b)| a + b),
        }
    }
}

impl<V, O> Add for &Value<V>
where
    for<'v> &'v V: Add<Output = O>,
{
    type Output = Value<O>;

    fn add(self, rhs: Self) -> Self::Output {
        Value {
            inner: self
                .inner
                .as_ref()
                .zip(rhs.inner.as_ref())
                .map(|(a, b)| a + b),
        }
    }
}

impl<V, O> Add<Value<&V>> for Value<V>
where
    for<'v> V: Add<&'v V, Output = O>,
{
    type Output = Value<O>;

    fn add(self, rhs: Value<&V>) -> Self::Output {
        Value {
            inner: self.inner.zip(rhs.inner).map(|(a, b)| a + b),
        }
    }
}

impl<V, O> Add<Value<V>> for Value<&V>
where
    for<'v> &'v V: Add<V, Output = O>,
{
    type Output = Value<O>;

    fn add(self, rhs: Value<V>) -> Self::Output {
        Value {
            inner: self.inner.zip(rhs.inner).map(|(a, b)| a + b),
        }
    }
}

impl<V, O> Add<&Value<V>> for Value<V>
where
    for<'v> V: Add<&'v V, Output = O>,
{
    type Output = Value<O>;

    fn add(self, rhs: &Self) -> Self::Output {
        self + rhs.as_ref()
    }
}

impl<V, O> Add<Value<V>> for &Value<V>
where
    for<'v> &'v V: Add<V, Output = O>,
{
    type Output = Value<O>;

    fn add(self, rhs: Value<V>) -> Self::Output {
        self.as_ref() + rhs
    }
}

impl<V, O> Add<&V> for Value<&V>
where
    for<'v> &'v V: Add<&'v V, Output = O>,
{
    type Output = Value<O>;

    fn add(self, rhs: &V) -> Self::Output {
        Value {
            inner: self.inner.map(|a| a + rhs),
        }
    }
}

impl<V, O> Add<&V> for Value<V>
where
    for<'v> V: Add<&'v V, Output = O>,
{
    type Output = Value<O>;

    fn add(self, rhs: &V) -> Self::Output {
        Value {
            inner: self.inner.map(|a| a + rhs),
        }
    }
}

impl<V, O> Add<V> for Value<&V>
where
    for<'v> &'v V: Add<V, Output = O>,
{
    type Output = Value<O>;

    fn add(self, rhs: V) -> Self::Output {
        Value {
            inner: self.inner.map(|a| a + rhs),
        }
    }
}

impl<V, O> Sub for Value<V>
where
    V: Sub<Output = O>,
{
    type Output = Value<O>;

    fn sub(self, rhs: Self) -> Self::Output {
        Value {
            inner: self.inner.zip(rhs.inner).map(|(a, b)| a - b),
        }
    }
}

impl<V, O> Sub for &Value<V>
where
    for<'v> &'v V: Sub<Output = O>,
{
    type Output = Value<O>;

    fn sub(self, rhs: Self) -> Self::Output {
        Value {
            inner: self
                .inner
                .as_ref()
                .zip(rhs.inner.as_ref())
                .map(|(a, b)| a - b),
        }
    }
}

impl<V, O> Sub<Value<&V>> for Value<V>
where
    for<'v> V: Sub<&'v V, Output = O>,
{
    type Output = Value<O>;

    fn sub(self, rhs: Value<&V>) -> Self::Output {
        Value {
            inner: self.inner.zip(rhs.inner).map(|(a, b)| a - b),
        }
    }
}

impl<V, O> Sub<Value<V>> for Value<&V>
where
    for<'v> &'v V: Sub<V, Output = O>,
{
    type Output = Value<O>;

    fn sub(self, rhs: Value<V>) -> Self::Output {
        Value {
            inner: self.inner.zip(rhs.inner).map(|(a, b)| a - b),
        }
    }
}

impl<V, O> Sub<&Value<V>> for Value<V>
where
    for<'v> V: Sub<&'v V, Output = O>,
{
    type Output = Value<O>;

    fn sub(self, rhs: &Self) -> Self::Output {
        self - rhs.as_ref()
    }
}

impl<V, O> Sub<Value<V>> for &Value<V>
where
    for<'v> &'v V: Sub<V, Output = O>,
{
    type Output = Value<O>;

    fn sub(self, rhs: Value<V>) -> Self::Output {
        self.as_ref() - rhs
    }
}

impl<V, O> Mul for Value<V>
where
    V: Mul<Output = O>,
{
    type Output = Value<O>;

    fn mul(self, rhs: Self) -> Self::Output {
        Value {
            inner: self.inner.zip(rhs.inner).map(|(a, b)| a * b),
        }
    }
}

impl<V, O> Mul for &Value<V>
where
    for<'v> &'v V: Mul<Output = O>,
{
    type Output = Value<O>;

    fn mul(self, rhs: Self) -> Self::Output {
        Value {
            inner: self
                .inner
                .as_ref()
                .zip(rhs.inner.as_ref())
                .map(|(a, b)| a * b),
        }
    }
}

impl<V, O> Mul<Value<&V>> for Value<V>
where
    for<'v> V: Mul<&'v V, Output = O>,
{
    type Output = Value<O>;

    fn mul(self, rhs: Value<&V>) -> Self::Output {
        Value {
            inner: self.inner.zip(rhs.inner).map(|(a, b)| a * b),
        }
    }
}

impl<V, O> Mul<Value<V>> for Value<&V>
where
    for<'v> &'v V: Mul<V, Output = O>,
{
    type Output = Value<O>;

    fn mul(self, rhs: Value<V>) -> Self::Output {
        Value {
            inner: self.inner.zip(rhs.inner).map(|(a, b)| a * b),
        }
    }
}

impl<V, O> Mul<&Value<V>> for Value<V>
where
    for<'v> V: Mul<&'v V, Output = O>,
{
    type Output = Value<O>;

    fn mul(self, rhs: &Self) -> Self::Output {
        self * rhs.as_ref()
    }
}

impl<V, O> Mul<Value<V>> for &Value<V>
where
    for<'v> &'v V: Mul<V, Output = O>,
{
    type Output = Value<O>;

    fn mul(self, rhs: Value<V>) -> Self::Output {
        self.as_ref() * rhs
    }
}
