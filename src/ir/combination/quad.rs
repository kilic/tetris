use crate::{
    ir::ac::AbstractCircuit, lc, Error, Field, QuadScaled, QuadVar, Scaled, Term, Value, Var,
};

use super::{linear::Lc, CombinationGadget, CombinationIR};

#[macro_export]
macro_rules! qc {
    () => {
        Qc::default()
    };
    ($constant:expr) => {
        Qc::new($constant)
    };
}

#[derive(Clone, Default, Debug)]
/// Quadratic-in-variable combination intermediate representation
pub struct Qc<F: Field> {
    pub(crate) lin: Vec<Scaled<F>>,
    pub(crate) quad: Vec<QuadScaled<F>>,
    pub(crate) constant: F,
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
/// `QcCoeff` is constant part of a linear combination.
pub struct QcCoeff<F: Field> {
    pub(crate) lin: Vec<F>,
    pub(crate) quad: Vec<F>,
    pub(crate) constant: F,
}

#[derive(Clone, Default)]
/// `QcVar` is variable part of a linear combination.
pub struct QcVar<F: Field> {
    pub lin: Vec<Var<F>>,
    pub quad: Vec<QuadVar<F>>,
}

impl<F: Field> CombinationIR<F> for Qc<F> {
    fn new(constant: F) -> Self {
        Self {
            lin: Vec::new(),
            quad: Vec::new(),
            constant,
        }
    }

    fn is_empty(&self) -> bool {
        self.lin.is_empty() && self.quad.is_empty()
    }

    fn value(&self) -> Value<F> {
        let u0 = Scaled::sum(&self.lin, self.constant);
        let u1 = QuadScaled::sum(&self.quad, F::zero());
        u0.zip(u1).map(|(u0, u1)| u0 + u1)
    }

    fn scale(&mut self, factor: F) {
        self.lin.iter_mut().for_each(|e| e.scale_assign(factor));
        self.quad.iter_mut().for_each(|e| e.scale_assign(factor));
        self.constant *= factor;
    }

    fn add_constant(&mut self, constant: F) {
        self.constant += constant;
    }
}

impl<F: Field> CombinationGadget<F, Qc<F>> for AbstractCircuit<F> {
    fn zero_sum(&mut self, e: Qc<F>) -> Result<(), Error> {
        self.sanity_ok(|| e.verify())?;
        (!e.is_empty()).then(|| match e.try_linear() {
            Some(lc) => {
                let (bases, vars) = lc.split();
                self.lc.entry(bases).or_default().push(vars);
            }
            None => {
                let (bases, vars) = e.split();
                self.qc.entry(bases).or_default().push(vars);
            }
        });
        Ok(())
    }

    fn eval(&mut self, mut qc: Qc<F>) -> Var<F> {
        // negate the sum and add
        let result = qc.value();
        let result = self.var(&result);
        qc -= result;
        self.zero_sum(qc).unwrap();
        result
    }
}

impl<F: Field> AbstractCircuit<F> {
    pub fn assign_bit(&mut self, w0: &Value<F>) -> Result<Var<F>, Error> {
        let w0 = self.var(w0);
        self.assert_bit(&w0)?;
        Ok(w0)
    }

    pub fn assert_bit(&mut self, w0: &Var<F>) -> Result<(), Error> {
        self.zero_sum(qc!() + w0 * w0 - w0)
    }

    pub fn mul(&mut self, w0: &Var<F>, w1: &Var<F>) -> Var<F> {
        self.eval(qc!() + w0 * w1)
    }

    pub fn mul_add(&mut self, w0: &Var<F>, w1: &Var<F>, to_add: &[Scaled<F>]) -> Var<F> {
        self.eval(qc!() + w0 * w1 + to_add)
    }

    pub fn assert_not_zero(&mut self, w: &Var<F>) -> Result<(), Error> {
        self.inv_incomplete(w).map(|_| ())
    }

    pub fn div_incomplete(&mut self, w0: &Var<F>, w1: &Var<F>) -> Result<Var<F>, Error> {
        let inv = w1.value().maybe(|w| w.inv())?;
        let res = w0.value() * inv;
        let res = self.var(&res);
        self.zero_sum(qc!() + w1 * res - w0)?;
        Ok(res)
    }

    pub fn inv_incomplete(&mut self, w: &Var<F>) -> Result<Var<F>, Error> {
        let inv = w.value().maybe(|w| w.inv())?;
        let inv = self.var(&inv);
        self.zero_sum(qc!(-F::one()) + inv * w)?;
        Ok(inv)
    }

    /// outputs `w0 + w1 - w0*w1`
    /// inputs must be bits otherwise it is unsound (eg: 2,2, 0)
    pub fn or(&mut self, w0: &Var<F>, w1: &Var<F>) -> Var<F> {
        self.eval(qc!() + w0 + w1 - w0 * w1)
    }

    /// outputs `w0 + w1 - 2*w0*w1`
    /// inputs must be bits otherwise it is unsound
    pub fn xor(&mut self, w0: &Var<F>, w1: &Var<F>) -> Var<F> {
        self.eval(qc!() + w0 + w1 - w0 * w1 * F::from_u64(2))
    }

    /// outputs `w0*w1`
    /// even inputs are not bits apply `is_zero` to output to get whether condition is met
    pub fn and(&mut self, w0: &Var<F>, w1: &Var<F>) -> Var<F> {
        self.mul(w0, w1)
    }

    pub fn inv(&mut self, w: &Var<F>) -> (Var<F>, Var<F>) {
        let (sign, inv) = w
            .value()
            .map(|w: F| {
                w.inv()
                    .map(|inverted| (F::zero(), inverted))
                    .unwrap_or_else(|| (F::one(), F::one()))
            })
            .unzip();
        let sign = self.var(&sign);
        let inv = self.var(&inv);

        self.zero_sum(qc!() + sign * inv - sign).unwrap();
        self.zero_sum(qc!() + w * sign).unwrap();
        (inv, sign)
    }

    pub fn is_zero(&mut self, w0: &Var<F>) -> Var<F> {
        self.inv(w0).1
    }

    pub fn is_one(&mut self, w0: &Var<F>) -> Var<F> {
        self.is_equal_to_constant(w0, F::one())
    }

    pub fn is_equal(&mut self, w0: &Var<F>, w1: &Var<F>) -> Var<F> {
        let u = self.sub(w0, w1);
        self.is_zero(&u)
    }

    pub fn is_equal_to_constant(&mut self, w0: &Var<F>, c: F) -> Var<F> {
        let t = self.eval(lc!(c) - w0);
        self.is_zero(&t)
    }

    pub fn assert_not_equal(&mut self, w0: &Var<F>, w1: &Var<F>) -> Result<(), Error> {
        let u = self.sub(w0, w1);
        self.assert_not_zero(&u)
    }

    pub fn select_constant(
        &mut self,
        cond: &Var<F>,
        w0: F, // cond = 0
        w1: F, // cond = 1
    ) -> Result<Var<F>, Error> {
        self.sanity_ok(|| {
            cond.value()
                .maybe(|c| (c.square() - *c).is_zero().then_some(()))
        })?;
        Ok(self.eval(lc!(w0) + cond * (w1 - w0)))
    }

    pub fn select_or_constant(
        &mut self,
        cond: &Var<F>,
        w0: F,       // cond = 0
        w1: &Var<F>, // cond = 1
    ) -> Result<Var<F>, Error> {
        self.sanity_ok(|| {
            cond.value()
                .maybe(|c| (c.square() - *c).is_zero().then_some(()))
        })?;
        Ok(self.eval(qc!(w0) + cond * w1 - cond * w0))
    }
}

impl<F: Field> Qc<F> {
    pub fn add_lin(&mut self, term: Scaled<F>) {
        self.lin.push(term);
    }

    pub fn add_quad(&mut self, term: QuadScaled<F>) {
        self.quad.push(term);
    }

    pub fn compose(e: &[Var<F>], limb_size: usize) -> Self {
        Self::horner(e, F::from_u64(1 << limb_size))
    }

    pub fn horner(e: &[Var<F>], coeff: F) -> Self {
        e.iter().rev().fold(qc!(), |mut acc, limb| {
            acc *= coeff;
            acc + limb
        })
    }

    pub(crate) fn filter_identity(&mut self) {
        self.lin.retain(|term| !term.is_identity());
        self.quad.retain(|term| !term.is_identity());
    }

    pub(crate) fn split(mut self) -> (QcCoeff<F>, QcVar<F>) {
        self.filter_identity();
        self.lin.sort();
        self.quad.sort();

        let bases = QcCoeff {
            lin: self.lin.iter().map(Term::coeff).collect(),
            quad: self.quad.iter().map(Term::coeff).collect(),
            constant: self.constant,
        };

        let lin = self.lin.iter().map(Term::var).cloned().collect();
        let quad = self.quad.iter().map(Term::var).cloned().collect();
        let variable = QcVar { lin, quad };

        (bases, variable)
    }

    pub(crate) fn try_linear(&self) -> Option<Lc<F>> {
        self.quad
            .is_empty()
            .then_some(lc!(self.constant) + &self.lin)
    }
}

impl<F: Field> std::ops::AddAssign<Qc<F>> for Qc<F> {
    fn add_assign(&mut self, qc: Qc<F>) {
        self.lin.extend_from_slice(&qc.lin);
        self.quad.extend_from_slice(&qc.quad);
        self.constant += qc.constant;
    }
}

impl<'a, F: Field> std::ops::MulAssign<&'a F> for Qc<F> {
    fn mul_assign(&mut self, factor: &F) {
        self.scale(*factor);
    }
}

impl<F: Field> std::ops::MulAssign<F> for Qc<F> {
    fn mul_assign(&mut self, factor: F) {
        self.scale(factor);
    }
}

impl<F: Field> std::ops::Neg for Qc<F> {
    type Output = Qc<F>;
    fn neg(self) -> Self::Output {
        let mut lc = self;
        lc.scale(-F::one());
        lc
    }
}

impl<F: Field, E> std::ops::Add<E> for Qc<F>
where
    Self: std::ops::AddAssign<E>,
{
    type Output = Qc<F>;
    fn add(self, term: E) -> Qc<F> {
        let mut lc = self;
        lc += term;
        lc
    }
}

impl<F: Field, E> std::ops::Sub<E> for Qc<F>
where
    Self: std::ops::SubAssign<E>,
{
    type Output = Qc<F>;
    fn sub(self, term: E) -> Qc<F> {
        let mut lc = self;
        lc -= term;
        lc
    }
}

impl<F: Field, I, E> std::ops::AddAssign<I> for Qc<F>
where
    I: IntoIterator<Item = E>,
    Self: std::ops::AddAssign<E>,
{
    fn add_assign(&mut self, terms: I) {
        terms.into_iter().for_each(|term| *self += term);
    }
}

impl<F: Field, I, E> std::ops::SubAssign<I> for Qc<F>
where
    I: IntoIterator<Item = E>,
    Self: std::ops::SubAssign<E>,
{
    fn sub_assign(&mut self, terms: I) {
        terms.into_iter().for_each(|term| *self -= term);
    }
}

impl<F: Field> From<Var<F>> for Qc<F> {
    fn from(e: Var<F>) -> Self {
        Qc {
            lin: std::iter::once(e.into()).collect(),
            ..Default::default()
        }
    }
}

impl<F: Field> From<&Var<F>> for Qc<F> {
    fn from(e: &Var<F>) -> Self {
        (*e).into()
    }
}

impl<F: Field> std::ops::AddAssign<Var<F>> for Qc<F> {
    fn add_assign(&mut self, term: Var<F>) {
        self.lin.push(term.into());
    }
}

impl<F: Field> std::ops::SubAssign<Var<F>> for Qc<F> {
    fn sub_assign(&mut self, term: Var<F>) {
        self.lin.push(-term);
    }
}

impl<F: Field> std::ops::AddAssign<&Var<F>> for Qc<F> {
    fn add_assign(&mut self, term: &Var<F>) {
        self.lin.push(term.into());
    }
}

impl<F: Field> std::ops::SubAssign<&Var<F>> for Qc<F> {
    fn sub_assign(&mut self, term: &Var<F>) {
        self.lin.push(-term);
    }
}

impl<F: Field> From<Scaled<F>> for Qc<F> {
    fn from(e: Scaled<F>) -> Self {
        Qc {
            lin: vec![e],
            ..Default::default()
        }
    }
}

impl<F: Field> From<&Scaled<F>> for Qc<F> {
    fn from(e: &Scaled<F>) -> Self {
        (*e).into()
    }
}

impl<F: Field> std::ops::AddAssign<Scaled<F>> for Qc<F> {
    fn add_assign(&mut self, term: Scaled<F>) {
        self.lin.push(term);
    }
}

impl<F: Field> std::ops::SubAssign<Scaled<F>> for Qc<F> {
    fn sub_assign(&mut self, term: Scaled<F>) {
        self.lin.push(-term);
    }
}

impl<F: Field> std::ops::AddAssign<&Scaled<F>> for Qc<F> {
    fn add_assign(&mut self, term: &Scaled<F>) {
        self.lin.push(*term);
    }
}

impl<F: Field> std::ops::SubAssign<&Scaled<F>> for Qc<F> {
    fn sub_assign(&mut self, term: &Scaled<F>) {
        self.lin.push(-term);
    }
}

impl<F: Field> From<QuadScaled<F>> for Qc<F> {
    fn from(e: QuadScaled<F>) -> Self {
        Qc {
            quad: std::iter::once(e).collect(),
            ..Default::default()
        }
    }
}

impl<F: Field> From<&QuadScaled<F>> for Qc<F> {
    fn from(e: &QuadScaled<F>) -> Self {
        (*e).into()
    }
}

impl<F: Field> std::ops::AddAssign<QuadScaled<F>> for Qc<F> {
    fn add_assign(&mut self, term: QuadScaled<F>) {
        self.quad.push(term);
    }
}

impl<F: Field> std::ops::SubAssign<QuadScaled<F>> for Qc<F> {
    fn sub_assign(&mut self, term: QuadScaled<F>) {
        self.quad.push(-term);
    }
}

impl<F: Field> std::ops::AddAssign<&QuadScaled<F>> for Qc<F> {
    fn add_assign(&mut self, term: &QuadScaled<F>) {
        self.quad.push(*term);
    }
}

impl<F: Field> std::ops::SubAssign<&QuadScaled<F>> for Qc<F> {
    fn sub_assign(&mut self, term: &QuadScaled<F>) {
        self.quad.push(-term);
    }
}
