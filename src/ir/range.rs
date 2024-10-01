use super::ac::{sanity_some, AbstractCircuit};
use crate::{utils::decompose_uint, Error, Field, Term, Value, Var};
use itertools::Itertools;
use num_bigint::BigUint;
use num_integer::div_ceil;
use num_traits::Zero;
use std::{
    collections::{BTreeMap, BTreeSet},
    vec,
};

#[derive(Clone, Debug)]
pub struct RcVar<F: Field> {
    pub limbs: Vec<Var<F>>,
    pub var: Var<F>,
}

impl<F: Field> RcVar<F> {
    pub fn new(var: &Var<F>, limbs: &[Var<F>]) -> RcVar<F> {
        RcVar {
            limbs: limbs.to_vec(),
            var: *var,
        }
    }

    pub fn unzip(&self) -> (&[Var<F>], &Var<F>) {
        (&self.limbs, &self.var)
    }

    pub fn concat(&self) -> Vec<Var<F>> {
        self.limbs
            .iter()
            .chain(std::iter::once(&self.var))
            .cloned()
            .collect()
    }

    pub fn limbs(&self) -> &[Var<F>] {
        &self.limbs
    }

    pub fn var(&self) -> &Var<F> {
        &self.var
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct RcCoeff {
    pub(crate) sizes: Vec<usize>,
    pub(crate) signed: bool,
}

impl RcCoeff {
    fn new(sizes: &[usize], signed: bool) -> RcCoeff {
        RcCoeff {
            sizes: sizes.to_vec(),
            signed,
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct RangeSingle {
    // size of the integer
    pub(crate) size: usize,
    // if signed range in [-2^size, 2^size-1]
    // else range is in [0, 2^size-1]
    pub(crate) signed: bool,
}

#[derive(Clone, Default)]
pub struct RangeIR<F: Field> {
    pub(crate) singles: BTreeMap<RangeSingle, Vec<Var<F>>>,
    pub(crate) combinations: BTreeMap<RcCoeff, Vec<RcVar<F>>>,
    pub(crate) sizes: BTreeSet<usize>,
}

impl<F: Field> RangeIR<F> {
    fn single(
        &mut self,
        sanity: bool,
        signed: bool,
        size: usize,
        var: &Var<F>,
    ) -> Result<(), Error> {
        var.value().maybe(|var| {
            sanity_some(sanity, || {
                use num_traits::One;
                let shift = if signed { 1 << size } else { 0 };
                let shift = F::from_u64(shift as u64);
                let max = size + if signed { 1 } else { 0 };
                let max = BigUint::one() << max;
                ((*var + shift).uint() < max).then_some(())
            })
        })?;
        let range = RangeSingle { size, signed };
        self.sizes.insert(size + if signed { 1 } else { 0 });
        self.singles.entry(range).or_default().push(*var);
        Ok(())
    }
}

impl<F: Field> AbstractCircuit<F> {
    fn new_range_combination(
        &mut self,
        signed: bool,
        sizes: &[usize],
        limbs: &[Value<F>],
        var: &Var<F>,
    ) -> Vec<Var<F>> {
        sizes.iter().for_each(|size| {
            assert_ne!(size, &0);
            self.range_ir
                .sizes
                .insert(size + if signed { 1 } else { 0 });
        });
        let limbs = limbs.iter().map(|limb| self.var(limb)).collect::<Vec<_>>();
        let var = RcVar::new(var, &limbs);
        let coeff = RcCoeff::new(sizes, signed);
        self.range_ir
            .combinations
            .entry(coeff)
            .or_default()
            .push(var);

        limbs
    }

    pub fn range_assign(&mut self, size: usize, value: &Value<F>) -> Result<Var<F>, Error> {
        assert_ne!(size, 0);
        let var = self.var(value);
        self.range(size, &var)?;
        Ok(var)
    }

    pub fn range_assign_signed(&mut self, size: usize, value: &Value<F>) -> Result<Var<F>, Error> {
        assert_ne!(size, 0);
        let var = self.var(value);
        self.range_signed(size, &var)?;
        Ok(var)
    }

    pub fn decompose_assign(
        &mut self,
        limb_size: usize,
        number_size: usize,
        value: &Value<F>,
    ) -> Result<Var<F>, Error> {
        assert_ne!(number_size, 0);
        let var = self.var(value);
        self.decompose(limb_size, number_size, &var).map(|_| var)
    }

    pub fn decompose_assign_signed(
        &mut self,
        limb_size: usize,
        number_size: usize,
        value: &Value<F>,
    ) -> Result<Var<F>, Error> {
        assert_ne!(number_size, 0);
        let var = self.var(value);
        self.decompose_signed(limb_size, number_size, &var)
            .map(|_| var)
    }

    pub fn range(&mut self, number_size: usize, var: &Var<F>) -> Result<(), Error> {
        self.range_ir.single(self.sanity, false, number_size, var)
    }

    pub fn range_signed(&mut self, size: usize, var: &Var<F>) -> Result<(), Error> {
        self.range_ir.single(self.sanity, true, size, var)
    }

    pub fn decompose(
        &mut self,
        limb_size: usize,
        number_size: usize,
        var: &Var<F>,
    ) -> Result<Vec<Var<F>>, Error> {
        if limb_size >= number_size {
            self.range_ir
                .single(self.sanity, false, number_size, var)
                .map(|_| vec![*var])
        } else {
            self._decompose(false, limb_size, number_size, var)
        }
    }

    pub fn decompose_signed(
        &mut self,
        limb_size: usize,
        number_size: usize,
        var: &Var<F>,
    ) -> Result<Vec<Var<F>>, Error> {
        if limb_size >= number_size {
            self.range_ir
                .single(self.sanity, true, number_size, var)
                .map(|_| vec![*var])
        } else {
            self._decompose(true, limb_size, number_size, var)
        }
    }

    pub fn decompose_nonuniform(
        &mut self,
        sizes: &[usize],
        var: &Var<F>,
    ) -> Result<Vec<Var<F>>, Error> {
        let n_limbs = sizes.len();
        let limbs = var
            .value()
            .maybe(|var| {
                let limbs = var.decompose_nonuniform(sizes);
                self.sanity_some(|| (F::compose_nonuniform(&limbs, sizes) == *var).then_some(()))
                    .map(|_| limbs)
            })?
            .transpose_vec(n_limbs);
        Ok(self.new_range_combination(false, sizes, &limbs, var))
    }

    fn _decompose(
        &mut self,
        signed: bool,
        limb_size: usize,
        number_size: usize,
        var: &Var<F>,
    ) -> Result<Vec<Var<F>>, Error> {
        assert!(limb_size > 0);
        assert!(number_size > limb_size);

        let n_limbs = div_ceil(number_size, limb_size);
        let mut e = number_size;
        let sizes = (0..n_limbs)
            .map(|_| {
                let size = e.min(limb_size);
                e = e.saturating_sub(limb_size);
                size
            })
            .collect_vec();

        let limbs = var
            .value()
            .maybe(|var| {
                if !signed {
                    let limbs = var.decompose(n_limbs, limb_size);
                    self.sanity_some(|| (F::compose(&limbs, limb_size) == *var).then_some(()))
                        .map(|_| limbs)
                } else {
                    use num_traits::One;
                    let bound = BigUint::one() << number_size;
                    let uint0 = var.uint();
                    let uint1 = var.neg().uint();
                    // positive case
                    let u0 = uint0 < bound;
                    // negative case
                    let u1 = uint1 < bound;

                    let limbs = match (u0, u1) {
                        // positive case
                        (true, false) => decompose_uint(&uint0, n_limbs, limb_size),
                        // negative case
                        (false, true) => {
                            let p = &self.modulus;
                            let limbs = decompose_uint(&uint1, n_limbs, limb_size);
                            limbs.iter().map(|e| (p - e) % p).collect()
                        }
                        // zero case
                        (true, true) => {
                            assert!(uint0.is_zero());
                            assert!(uint1.is_zero());
                            vec![BigUint::zero(); n_limbs]
                        }
                        // Must fail in sanity check
                        _ => vec![BigUint::zero(); n_limbs],
                    };

                    let limbs = limbs
                        .iter()
                        .map(F::from_uint)
                        .collect::<Result<Vec<_>, _>>()
                        .unwrap();

                    self.sanity_some(|| (F::compose(&limbs, limb_size) == *var).then_some(()))
                        .map(|_| limbs)
                }
            })?
            .transpose_vec(n_limbs);

        Ok(self.new_range_combination(signed, &sizes, &limbs, var))
    }
}
