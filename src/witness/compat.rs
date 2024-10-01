#[cfg(feature = "halo2")]
pub mod halo2 {
    use num_bigint::BigUint;

    use crate::{Error, Field};

    pub mod utils {
        use crate::Error;
        use halo2_proofs::halo2curves::ff::PrimeField;
        use num_bigint::BigUint;
        pub fn to_uint<F: PrimeField>(fe: &F) -> BigUint {
            BigUint::from_bytes_le(fe.to_repr().as_ref())
        }
        pub fn modulus<F: PrimeField>() -> BigUint {
            to_uint(&-F::ONE) + 1usize
        }
        pub fn from_uint_red<F: PrimeField>(e: &BigUint) -> F {
            let modulus = modulus::<F>();
            let e = e % modulus;
            from_uint(&e).unwrap()
        }
        pub fn from_uint<F: PrimeField>(e: &BigUint) -> Result<F, Error> {
            let bytes = e.to_bytes_le();
            let mut repr = F::Repr::default();
            (repr.as_ref().len() >= bytes.len())
                .then_some(())
                .ok_or(Error::Invalid)?;
            repr.as_mut()[..bytes.len()].copy_from_slice(&bytes[..]);
            F::from_repr(repr).into_option().ok_or(Error::Invalid)
        }
    }

    impl<T: halo2_proofs::halo2curves::ff::PrimeField + Ord> Field for T {
        fn one() -> Self {
            T::ONE
        }
        fn num_bits() -> usize {
            T::NUM_BITS as usize
        }
        fn zero() -> Self {
            T::ZERO
        }
        #[cfg(test)]
        fn rand(rng: &mut impl rand::RngCore) -> Self {
            T::random(rng)
        }
        fn inv(&self) -> Option<Self> {
            self.invert().into()
        }
        fn uint(&self) -> BigUint {
            utils::to_uint(self)
        }
        fn from_u64(n: u64) -> Self {
            n.into()
        }
        fn from_uint(big: &BigUint) -> Result<Self, Error> {
            utils::from_uint(big)
        }
        fn from_uint_red(big: &BigUint) -> Self {
            utils::from_uint_red(big)
        }
    }
}

#[cfg(feature = "arkworks")]
pub mod arkworks {
    use crate::{Error, Field};
    use num_bigint::BigUint;

    pub mod utils {
        use crate::witness::field::Field;
        use crate::Error;
        use ark_ff::PrimeField;
        use num_bigint::BigUint;
        pub fn to_uint<F: PrimeField>(fe: &F) -> BigUint {
            (*fe).into()
        }
        pub fn modulus<F: PrimeField>() -> BigUint {
            to_uint(&-F::ONE) + 1usize
        }
        pub fn from_uint_red<F: PrimeField>(e: &BigUint) -> F {
            let bytes = e.to_bytes_be();
            F::from_be_bytes_mod_order(&bytes)
        }
        pub fn from_uint<F: PrimeField>(e: &BigUint) -> Result<F, Error> {
            let bytes = e
                .to_bytes_le()
                .into_iter()
                .chain(std::iter::repeat(0u8))
                .take(F::num_bytes())
                .collect::<Vec<_>>();
            F::deserialize_uncompressed(&bytes[..]).map_err(|_| Error::Invalid)
        }
    }

    impl<T: ark_ff::PrimeField + Ord> Field for T {
        fn one() -> Self {
            T::ONE
        }
        fn num_bits() -> usize {
            T::MODULUS_BIT_SIZE as usize
        }
        fn zero() -> Self {
            T::ZERO
        }
        #[cfg(test)]
        fn rand(rng: &mut impl rand::RngCore) -> Self {
            T::rand(rng)
        }
        fn inv(&self) -> Option<Self> {
            self.inverse()
        }
        fn uint(&self) -> BigUint {
            utils::to_uint(self)
        }
        fn from_u64(n: u64) -> Self {
            n.into()
        }
        fn from_uint(big: &BigUint) -> Result<Self, Error> {
            utils::from_uint(big)
        }
        fn from_uint_red(big: &BigUint) -> Self {
            utils::from_uint_red(big)
        }
    }
}

#[cfg(feature = "p3")]
pub mod p3 {
    use crate::{Error, Field};
    use num_bigint::BigUint;
    pub mod utils {
        use crate::Error;
        use num_bigint::BigUint;
        use p3_field::PrimeField;
        pub fn to_uint<F: PrimeField>(fe: &F) -> BigUint {
            fe.as_canonical_biguint()
        }
        pub fn modulus<F: PrimeField>() -> BigUint {
            to_uint(&-F::one()) + 1usize
        }

        pub fn from_uint_red<F: PrimeField>(e: &BigUint) -> F {
            let e = e % F::order();
            F::from_canonical_u64(e.try_into().unwrap())
        }

        pub fn from_uint<F: PrimeField>(e: &BigUint) -> Result<F, Error> {
            e.try_into()
                .map(F::from_canonical_u64)
                .map_err(|_| Error::Invalid)
        }
    }

    impl<T: p3_field::PrimeField + Ord> Field for T {
        fn one() -> Self {
            T::one()
        }
        fn num_bits() -> usize {
            T::bits()
        }
        fn zero() -> Self {
            T::zero()
        }
        fn from_u64(n: u64) -> Self {
            T::from_canonical_u64(n)
        }
        fn inv(&self) -> Option<Self> {
            self.try_inverse()
        }
        fn uint(&self) -> BigUint {
            utils::to_uint(self)
        }
        fn from_uint(big: &BigUint) -> Result<Self, Error> {
            utils::from_uint(big)
        }
        fn from_uint_red(big: &BigUint) -> Self {
            utils::from_uint_red(big)
        }
    }
}
