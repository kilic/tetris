use super::{CombinationGadget, CombinationIR};
use crate::{ir::ac::AbstractCircuit, Error, Field, Scaled, Term, Value, Var};
use itertools::izip;
use std::ops::Not;

#[macro_export]
macro_rules! lc {
    () => {
        Lc::default()
    };
    ($constant:expr) => {
        Lc::new($constant)
    };
}

#[derive(Default, Clone, Debug)]
/// Linear-in-variable combination intermediate representation
pub struct Lc<F: Field> {
    pub(crate) terms: Vec<Scaled<F>>,
    pub(crate) constant: F,
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
/// `LcCoeff` is constant part of a linear combination.
pub struct LcCoeff<F> {
    pub(crate) coeffs: Vec<F>,
    pub(crate) constant: F,
}

/// `LcVar` is variable part of a linear combination.
pub type LcVar<F> = Vec<Var<F>>;

impl<F: Field> CombinationIR<F> for Lc<F> {
    fn new(constant: F) -> Self {
        Self {
            terms: Vec::new(),
            constant,
        }
    }

    fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    fn value(&self) -> Value<F> {
        Scaled::sum(&self.terms, self.constant)
    }

    fn scale(&mut self, factor: F) {
        self.terms.iter_mut().for_each(|e| e.scale_assign(factor));
        self.constant *= factor;
    }

    fn add_constant(&mut self, constant: F) {
        self.constant += constant;
    }
}

impl<F: Field> CombinationGadget<F, Lc<F>> for AbstractCircuit<F> {
    fn zero_sum(&mut self, e: Lc<F>) -> Result<(), Error> {
        self.sanity_ok(|| e.verify())?;
        (!e.is_empty()).then(|| {
            let (bases, vars) = e.split();
            self.lc.entry(bases).or_default().push(vars);
        });

        Ok(())
    }

    fn eval(&mut self, mut lc: Lc<F>) -> Var<F> {
        // negate the sum and add
        let result = lc.value();
        let result = self.var(&result);
        lc -= result;

        self.zero_sum(lc).unwrap();
        result
    }
}

impl<F: Field> AbstractCircuit<F> {
    pub fn assign(&mut self, value: &Value<F>) -> Var<F> {
        let w = self.var(value);
        self.zero_sum(lc!() + w * F::zero()).unwrap();
        w
    }

    pub fn equal_to_constant(&mut self, w0: &Var<F>, constant: F) -> Result<(), Error> {
        self.zero_sum(lc!(-constant) + w0)
    }

    pub fn assert_zero(&mut self, w0: &Var<F>) -> Result<(), Error> {
        self.equal_to_constant(w0, F::zero())
    }

    pub fn scale(&mut self, w0: &Scaled<F>) -> Var<F> {
        let lc: Lc<F> = w0.into();
        self.eval(lc)
    }

    pub fn assert_one(&mut self, w0: &Var<F>) -> Result<(), Error> {
        self.equal_to_constant(w0, F::one())
    }

    pub fn add(&mut self, w0: &Var<F>, w1: &Var<F>) -> Var<F> {
        self.eval(lc!() + w0 + w1)
    }

    pub fn add_constant(&mut self, w0: &Var<F>, constant: F) -> Var<F> {
        self.eval(lc!(constant) + w0)
    }

    pub fn sub(&mut self, w0: &Var<F>, w1: &Var<F>) -> Var<F> {
        self.eval(lc!() + w0 - w1)
    }

    pub fn compose(&mut self, e: &[Var<F>], limb_size: usize) -> Var<F> {
        self.horner(e, F::from_u64(1u64 << limb_size))
    }

    pub fn compose_nonuniform(&mut self, e: &[Var<F>], sizes: &[usize]) -> Var<F> {
        assert_eq!(e.len(), sizes.len());

        // let lc = {
        //     let mut shift = 0;
        //     let terms = izip!(e, sizes).map(|(e, size)| {
        //         assert_ne!(size, &0);
        //         let term = e * F::from_u64(1 << shift); // FIX: shift goes beyond 64 bits
        //         shift += size;
        //         term
        //     });
        //     lc!() + terms
        // };

        sizes.iter().for_each(|size| assert_ne!(size, &0));
        let lc = izip!(e, sizes).rev().fold(lc!(), |mut acc, (val, size)| {
            assert_ne!(size, &0);
            acc *= F::from_u64(1 << size);
            acc + val
        });
        self.eval(lc)
    }

    pub fn horner(&mut self, e: &[Var<F>], coeff: F) -> Var<F> {
        let lc = e.iter().rev().fold(lc!(), |mut acc, limb| {
            acc *= coeff;
            acc + limb
        });
        self.eval(lc)
    }

    pub fn one(&mut self) -> Var<F> {
        self.get_constant(F::one())
    }

    pub fn zero(&mut self) -> Var<F> {
        self.get_constant(F::zero())
    }
}

impl<F: Field> Lc<F> {
    pub fn new(constant: F) -> Self {
        Self {
            terms: Vec::new(),
            constant,
        }
    }

    pub(crate) fn is_atomic(&self) -> bool {
        self.terms.len() == 1 && self.constant == F::zero()
    }

    pub(crate) fn filter_identity(&mut self) {
        self.is_atomic()
            .not()
            .then(|| self.terms.retain(|term| !term.is_identity()));
    }

    pub(crate) fn split(mut self) -> (LcCoeff<F>, LcVar<F>) {
        self.filter_identity();
        self.terms.sort();
        let coeffs = self.terms.iter().map(Term::coeff).collect();
        let coeffs = LcCoeff {
            coeffs,
            constant: self.constant,
        };
        let var = self
            .terms
            .iter()
            .map(Term::var)
            .cloned()
            .collect::<Vec<_>>();
        (coeffs, var)
    }
}

impl<'a, F: Field> std::ops::MulAssign<&'a F> for Lc<F> {
    fn mul_assign(&mut self, factor: &F) {
        self.scale(*factor);
    }
}

impl<F: Field> std::ops::MulAssign<F> for Lc<F> {
    fn mul_assign(&mut self, factor: F) {
        self.scale(factor);
    }
}

impl<F: Field> std::ops::Neg for Lc<F> {
    type Output = Lc<F>;
    fn neg(self) -> Self::Output {
        let mut lc = self;
        lc.scale(-F::one());
        lc
    }
}

impl<F: Field, E> std::ops::Add<E> for Lc<F>
where
    Self: std::ops::AddAssign<E>,
{
    type Output = Lc<F>;
    fn add(self, term: E) -> Lc<F> {
        let mut lc = self;
        lc += term;
        lc
    }
}

impl<F: Field, E> std::ops::Sub<E> for Lc<F>
where
    Self: std::ops::SubAssign<E>,
{
    type Output = Lc<F>;
    fn sub(self, term: E) -> Lc<F> {
        let mut lc = self;
        lc -= term;
        lc
    }
}

impl<F: Field, I, E> std::ops::AddAssign<I> for Lc<F>
where
    I: IntoIterator<Item = E>,
    Self: std::ops::AddAssign<E>,
{
    fn add_assign(&mut self, terms: I) {
        terms.into_iter().for_each(|term| *self += term);
    }
}

impl<F: Field, I, E> std::ops::SubAssign<I> for Lc<F>
where
    I: IntoIterator<Item = E>,
    Self: std::ops::SubAssign<E>,
{
    fn sub_assign(&mut self, terms: I) {
        terms.into_iter().for_each(|term| *self -= term);
    }
}

impl<F: Field> From<Var<F>> for Lc<F> {
    fn from(e: Var<F>) -> Self {
        Lc {
            terms: std::iter::once(e.into()).collect(),
            ..Default::default()
        }
    }
}

impl<F: Field> From<&Var<F>> for Lc<F> {
    fn from(e: &Var<F>) -> Self {
        (*e).into()
    }
}

impl<F: Field> std::ops::AddAssign<Var<F>> for Lc<F> {
    fn add_assign(&mut self, term: Var<F>) {
        self.terms.push(term.into());
    }
}

impl<F: Field> std::ops::SubAssign<Var<F>> for Lc<F> {
    fn sub_assign(&mut self, term: Var<F>) {
        self.terms.push(-term);
    }
}

impl<F: Field> std::ops::AddAssign<&Var<F>> for Lc<F> {
    fn add_assign(&mut self, term: &Var<F>) {
        self.terms.push(term.into());
    }
}

impl<F: Field> std::ops::SubAssign<&Var<F>> for Lc<F> {
    fn sub_assign(&mut self, term: &Var<F>) {
        self.terms.push(-term);
    }
}

impl<F: Field> From<Scaled<F>> for Lc<F> {
    fn from(e: Scaled<F>) -> Self {
        Lc {
            terms: std::iter::once(e).collect(),
            constant: Default::default(),
        }
    }
}

impl<F: Field> From<&Scaled<F>> for Lc<F> {
    fn from(e: &Scaled<F>) -> Self {
        (*e).into()
    }
}

impl<F: Field> std::ops::AddAssign<Scaled<F>> for Lc<F> {
    fn add_assign(&mut self, term: Scaled<F>) {
        self.terms.push(term);
    }
}

impl<F: Field> std::ops::SubAssign<Scaled<F>> for Lc<F> {
    fn sub_assign(&mut self, term: Scaled<F>) {
        self.terms.push(-term);
    }
}

impl<F: Field> std::ops::AddAssign<&Scaled<F>> for Lc<F> {
    fn add_assign(&mut self, term: &Scaled<F>) {
        self.terms.push(*term);
    }
}

impl<F: Field> std::ops::SubAssign<&Scaled<F>> for Lc<F> {
    fn sub_assign(&mut self, term: &Scaled<F>) {
        self.terms.push(-term);
    }
}
