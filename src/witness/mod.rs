use field::Field;
use num_bigint::{BigInt, BigUint};
use value::Value;

pub mod binops;
pub mod compat;
pub mod field;
pub mod value;

pub trait Term<F: Field>: Sized + std::fmt::Debug {
    type Scaled: Term<F>;
    type Var;

    fn value(&self) -> Value<F>;

    fn coeff(&self) -> F;

    fn is_identity(&self) -> bool {
        self.coeff().is_zero()
    }

    fn var(&self) -> &Self::Var;

    fn sum(terms: &[Self], constant: F) -> Value<F> {
        terms.iter().fold(constant.into(), |acc, term| {
            acc.zip(term.value()).map(|(acc, coeff)| acc + coeff)
        })
    }

    fn decompose(&self, n_limbs: usize, limb_size: usize) -> Value<Vec<F>> {
        self.value()
            .as_ref()
            .map(|value| value.decompose(n_limbs, limb_size))
    }

    fn uint(&self) -> Value<BigUint> {
        self.value().as_ref().map(Field::uint)
    }

    fn int(&self) -> Value<BigInt> {
        self.value().as_ref().map(Field::int)
    }

    fn eq(&self, other: &Self) -> Value<bool> {
        self.value().zip(other.value()).map(|(a, b)| a == b)
    }

    fn transpose<'a, I: IntoIterator<Item = &'a Self>>(iter: I) -> Value<Vec<F>>
    where
        Self: 'a,
    {
        let iter = iter.into_iter().map(|e| e.value()).collect::<Vec<_>>();
        Value::from_iter(iter)
    }
}

#[derive(Clone, Copy)]
pub struct Var<F> {
    pub(crate) id: Option<u64>,
    pub(crate) value: Value<F>,
}

impl<F: Field> Default for Var<F> {
    fn default() -> Self {
        Self {
            id: None,
            value: Value::empty(),
        }
    }
}

impl<F: Field> AsRef<Var<F>> for Var<F> {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<F: Field> Term<F> for Var<F> {
    type Scaled = Scaled<F>;
    type Var = Self;

    fn value(&self) -> Value<F> {
        self.value
    }

    fn var(&self) -> &Self::Var {
        self
    }

    fn coeff(&self) -> F {
        F::one()
    }
}

impl<F: Field> std::fmt::Debug for Var<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug = f.debug_struct("Var");
        if let Some(id) = self.id {
            debug.field("id", &id);
        } else {
            debug.field("id", &"tmp");
        }
        self.value.as_ref().map(|value| {
            let value = value.uint();
            let modulus = F::modulus();
            let neg = &modulus - &value;
            if neg < BigUint::from(1usize) << 64 {
                debug.field("value", &format!("-{}", neg.to_str_radix(16)));
                debug.field("bits", &neg.bits());
            } else {
                debug.field("value", &value.to_str_radix(16));
                debug.field("bits", &value.bits());
            }
        });
        debug.finish()
    }
}

impl<F: Field> Var<F> {
    pub fn new(id: u64, value: &Value<F>) -> Self {
        Var {
            id: Some(id),
            value: *value,
        }
    }

    pub fn tmp(value: Value<F>) -> Self {
        Var { id: None, value }
    }

    pub fn id(&self) -> Option<u64> {
        self.id
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Scaled<F: Field> {
    pub(crate) coeff: F,
    pub(crate) var: Var<F>,
}

impl<F: Field> AsRef<Scaled<F>> for Scaled<F> {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<F: Field> Scaled<F> {
    pub fn new(var: &Var<F>, coeff: F) -> Self {
        Self { var: *var, coeff }
    }

    pub fn tmp(value: Value<F>, scale: F) -> Self {
        Self::new(&Var::tmp(value), scale)
    }

    pub fn scale_assign(&mut self, coeff: F) {
        self.coeff *= coeff;
    }

    pub fn neg_assign(&mut self) {
        self.coeff = -self.coeff;
    }
}

impl<F: Field> Term<F> for Scaled<F> {
    type Scaled = Self;
    type Var = Var<F>;

    fn value(&self) -> Value<F> {
        self.var.value.as_ref().map(|e| self.coeff * *e)
    }

    fn var(&self) -> &Self::Var {
        &self.var
    }

    fn coeff(&self) -> F {
        self.coeff
    }
}

impl<F: Field> From<Var<F>> for Scaled<F> {
    fn from(var: Var<F>) -> Self {
        Self::new(&var, F::one())
    }
}

impl<F: Field> From<&Var<F>> for Scaled<F> {
    fn from(var: &Var<F>) -> Self {
        Self::new(var, F::one())
    }
}

// Warning: PartialEq implementation is for ordering don't use it for equality
impl<F: Field> PartialEq for Scaled<F> {
    fn eq(&self, other: &Self) -> bool {
        self.coeff == other.coeff
    }
}

// Warning: Eq implementation is for ordering don't use it for equality
impl<F: Field> Eq for Scaled<F> {}

impl<F: Field> PartialOrd for Scaled<F> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: Field> Ord for Scaled<F> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.coeff.cmp(&other.coeff)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct QuadVar<F: Field> {
    pub(crate) var0: Var<F>,
    pub(crate) var1: Var<F>,
}

impl<F: Field> AsRef<QuadVar<F>> for QuadVar<F> {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<F: Field> QuadVar<F> {
    pub fn new(var0: &Var<F>, var1: &Var<F>) -> Self {
        Self {
            var0: *var0,
            var1: *var1,
        }
    }

    pub fn var0(&self) -> &Var<F> {
        &self.var0
    }

    pub fn var1(&self) -> &Var<F> {
        &self.var1
    }
}

impl<F: Field> Term<F> for QuadVar<F> {
    type Scaled = Self;
    type Var = QuadVar<F>;

    fn value(&self) -> Value<F> {
        self.var0()
            .value()
            .zip(self.var1().value())
            .map(|(var0, var1)| var0 * var1)
    }

    fn coeff(&self) -> F {
        F::one()
    }

    fn var(&self) -> &Self::Var {
        self
    }
}

#[derive(Clone, Copy, Debug)]
pub struct QuadScaled<F: Field> {
    pub(crate) coeff: F,
    pub(crate) var: QuadVar<F>,
}

impl<F: Field> AsRef<QuadScaled<F>> for QuadScaled<F> {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<F: Field> QuadScaled<F> {
    pub fn new(var0: &Var<F>, var1: &Var<F>, coeff: F) -> Self {
        Self {
            var: QuadVar::new(var0, var1),
            coeff,
        }
    }

    pub fn var0(&self) -> &Var<F> {
        &self.var.var0
    }

    pub fn var1(&self) -> &Var<F> {
        &self.var.var1
    }

    pub fn scale_assign(&mut self, coeff: F) {
        self.coeff *= coeff;
    }

    pub fn neg_assign(&mut self) {
        self.coeff = -self.coeff;
    }
}

impl<F: Field> Term<F> for QuadScaled<F> {
    type Scaled = Self;
    type Var = QuadVar<F>;

    fn value(&self) -> Value<F> {
        self.var.value().map(|w| w * self.coeff)
    }

    fn coeff(&self) -> F {
        self.coeff
    }

    fn var(&self) -> &Self::Var {
        &self.var
    }
}

// Warning: PartialEq implementation is for ordering don't use it for equality
impl<F: Field> PartialEq for QuadScaled<F> {
    fn eq(&self, other: &Self) -> bool {
        self.coeff == other.coeff
    }
}

// Warning: Eq implementation is for ordering don't use it for equality
impl<F: Field> Eq for QuadScaled<F> {}

impl<F: Field> PartialOrd for QuadScaled<F> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: Field> Ord for QuadScaled<F> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.coeff.cmp(&other.coeff)
    }
}
