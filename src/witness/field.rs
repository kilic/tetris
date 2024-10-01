use crate::{
    utils::{decompose_uint, decompose_uint_nonuniform},
    Error,
};
use itertools::{izip, Itertools};
#[cfg(test)]
use num_bigint::RandBigInt;
use num_bigint::{BigInt, BigUint};
use num_traits::One;
#[cfg(test)]
use rand::RngCore;

pub trait Field:
    Eq
    + Ord
    + Copy
    + Clone
    + Default
    + Send
    + Sync
    + std::fmt::Debug
    + std::ops::Neg<Output = Self>
    + std::ops::Add<Output = Self>
    + std::ops::Sub<Output = Self>
    + std::ops::Mul<Output = Self>
    + std::iter::Sum
    + std::iter::Product
    + std::ops::AddAssign
    + std::ops::SubAssign
    + std::ops::MulAssign
{
    fn num_bits() -> usize;

    fn num_bytes() -> usize {
        (Self::num_bits() + 7) / 8
    }

    fn inv(&self) -> Option<Self>;

    fn one() -> Self {
        Self::from_u64(1u64)
    }

    fn from_u64(n: u64) -> Self;

    fn zero() -> Self {
        Self::from_u64(0u64)
    }

    fn is_zero(&self) -> bool {
        *self == Self::zero()
    }

    fn double(&self) -> Self {
        *self + *self
    }

    fn square(&self) -> Self {
        *self * *self
    }

    fn pow<S: AsRef<[u64]>>(&self, exp: S) -> Self {
        use num_integer::Integer;
        let mut res = Self::one();
        for e in exp.as_ref().iter().rev() {
            (0..64).rev().for_each(|i| {
                res = res.square();
                (*e >> i).is_odd().then(|| res.mul_assign(*self));
            });
        }
        res
    }

    fn uint(&self) -> BigUint;
    fn int(&self) -> BigInt {
        self.uint().into()
    }
    fn from_uint(int: &BigUint) -> Result<Self, Error>;
    fn from_uint_red(int: &BigUint) -> Self;
    fn from_int(int: &BigInt) -> Result<Self, Error> {
        use num_bigint::Sign;
        match int.sign() {
            Sign::Minus => Ok(Self::from_uint(int.magnitude())?.neg()),
            Sign::Plus => Self::from_uint(int.magnitude()),
            Sign::NoSign => Ok(Self::zero()),
        }
    }

    fn from_int_red(int: &BigInt) -> Self {
        use num_bigint::Sign;
        match int.sign() {
            Sign::Minus => Self::from_uint_red(int.magnitude()).neg(),
            Sign::Plus => Self::from_uint_red(int.magnitude()),
            Sign::NoSign => Self::zero(),
        }
    }

    fn modulus() -> BigUint {
        (-Self::one()).uint() + 1usize
    }

    fn cast<W: Field>(&self) -> W {
        W::from_uint_red(&self.uint())
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        Self::from_uint(&BigUint::from_bytes_le(bytes))
    }

    fn from_bytes_red(bytes: &[u8]) -> Self {
        Self::from_uint_red(&BigUint::from_bytes_le(bytes))
    }

    fn decompose(&self, n_limbs: usize, limb_size: usize) -> Vec<Self> {
        decompose_uint(&self.uint(), n_limbs, limb_size)
            .iter()
            .map(Self::from_uint)
            .try_collect()
            .unwrap()
    }

    fn decompose_nonuniform(&self, sizes: &[usize]) -> Vec<Self> {
        decompose_uint_nonuniform(&self.uint(), sizes)
            .iter()
            .map(Self::from_uint)
            .try_collect()
            .unwrap()
    }

    fn compose(input: &[Self], limb_size: usize) -> Self {
        let r = BigUint::one() << limb_size;
        let r = Self::from_uint(&r).unwrap();
        input
            .iter()
            .rev()
            .fold(Self::zero(), |acc, val| (acc * r) + *val)
    }

    fn compose_nonuniform(e: &[Self], sizes: &[usize]) -> Self {
        assert_eq!(e.len(), sizes.len());
        sizes.iter().for_each(|size| assert_ne!(size, &0));
        let r = Self::from_u64(2);
        izip!(e, sizes)
            .rev()
            .fold(Self::zero(), |acc, (val, size)| {
                (acc * r.pow(vec![*size as u64])) + *val
            })
    }

    #[cfg(test)]
    fn rand(rng: &mut impl RngCore) -> Self {
        Self::from_uint_red(&rng.gen_biguint(2 * Self::num_bits() as u64))
    }

    #[cfg(test)]
    fn rand_in_range(mut rng: impl RngCore, signed: bool, size: usize) -> Self {
        assert!(size <= Self::num_bits());
        let e = &rng.gen_biguint(size as u64);
        let e = Self::from_uint(e).unwrap();
        use rand::Rng;
        if signed & rng.gen_bool(0.5) {
            -e
        } else {
            e
        }
    }

    #[cfg(test)]
    fn hex(&self) -> String {
        let bytes = self
            .uint()
            .to_bytes_le()
            .into_iter()
            .chain(std::iter::repeat(0))
            .take(Self::num_bytes())
            .collect_vec();
        let bytes = bytes.into_iter().rev().collect::<Vec<_>>();
        hex::encode(&bytes)
    }
}
