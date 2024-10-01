use crate::Field;
use num_bigint::BigUint;
use rand::RngCore;

use super::Point;

pub trait Curve:
    Sized
    + std::fmt::Debug
    + Eq
    + PartialEq
    + Copy
    + Clone
    + Default
    + Send
    + Sync
    + std::fmt::Debug
    + std::ops::Neg<Output = Self>
    + std::ops::Add<Output = Self>
    + std::ops::Sub<Output = Self>
    + std::ops::Mul<Self::Scalar, Output = Self>
{
    type Scalar: Field;
    type Base: Field;

    fn rand(rng: &mut impl RngCore) -> Self;
    fn double(&self) -> Self;
    fn identity() -> Self;
    fn b() -> BigUint;
    fn coords(&self) -> Point<Self::Base>;
    fn from_coords(x: &Self::Base, y: &Self::Base) -> Option<Self>;
    fn generator() -> Self;
    fn sum(points: &[Self]) -> Self {
        points.iter().fold(Self::identity(), |acc, p| acc + *p)
    }
    fn incremental_table(&self, size: usize, aux: &Self) -> Vec<Self> {
        assert!(size > 0);
        std::iter::successors(Some(*aux), |suc| Some(*suc + *self))
            .take(size)
            .collect()
    }
    fn to_bytes(&self) -> Vec<u8>;
    fn hash_to_curve(person: &str, msg: &[u8]) -> Self;
    fn extended_table(&self, aux: &Self, window: usize) -> (Vec<Vec<Self>>, Self) {
        let table_size = 1 << window;
        let table = self.incremental_table(table_size, &Self::identity());
        let n_rounds = num_integer::div_ceil(Self::Scalar::num_bits(), window);
        let tables = std::iter::successors(Some(table.to_vec()), |succ| {
            Some(
                succ.iter()
                    .map(|p| (0..window).fold(*p, |acc, _| acc.double()))
                    .collect(),
            )
        })
        .take(n_rounds);
        let aux = aux.incremental_table(n_rounds, aux);
        let tables = tables
            .zip(aux.iter())
            .map(|(table, aux)| table.iter().map(|p| *p + *aux).collect::<Vec<_>>())
            .collect();
        (tables, Self::sum(&aux))
    }
}

#[cfg(feature = "halo2")]
pub mod halo2 {

    use crate::gadget::ecc::Point;

    use super::Curve;
    use crate::Field;
    use halo2_proofs::halo2curves::ff::PrimeField;
    use halo2_proofs::halo2curves::group::Group;
    use halo2_proofs::halo2curves::Coordinates;
    use num_bigint::BigUint;
    use rand::RngCore;

    impl<
            Base: PrimeField + Ord,
            A: halo2_proofs::halo2curves::CurveAffine<Base = Base, CurveExt = T>,
            T: halo2_proofs::halo2curves::CurveExt<AffineExt = A, Base = Base>,
        > Curve for T
    where
        T::Scalar: Ord,
    {
        type Scalar = <T as Group>::Scalar;
        type Base = Base;

        fn hash_to_curve(person: &str, msg: &[u8]) -> Self {
            Self::hash_to_curve(person)(msg)
        }
        fn generator() -> Self {
            T::generator()
        }
        fn to_bytes(&self) -> Vec<u8> {
            self.to_affine().to_bytes().as_ref().to_vec()
        }
        fn b() -> BigUint {
            T::b().uint()
        }
        fn rand(rng: &mut impl RngCore) -> Self {
            T::random(rng)
        }
        fn identity() -> Self {
            T::identity()
        }
        fn coords(&self) -> Point<T::Base> {
            let coords: Coordinates<_> = self.to_affine().coordinates().unwrap();
            Point::new(*coords.x(), *coords.y())
        }
        fn from_coords(x: &Base, y: &Base) -> Option<Self> {
            T::Affine::from_xy(*x, *y).map(|p| p.to_curve()).into()
        }
        fn double(&self) -> Self {
            self.double()
        }
    }
}

#[cfg(feature = "arkworks")]
pub mod arkworks {
    use super::Curve;
    use crate::gadget::ecc::Point;
    use crate::Field;
    use ark_ec::{
        short_weierstrass::{Affine, Projective, SWCurveConfig},
        AffineRepr, CurveGroup,
    };
    use ark_ff::{PrimeField, UniformRand};
    use ark_serialize::CanonicalSerialize;
    use num_bigint::BigUint;
    use rand::RngCore;
    use sha2::{Digest, Sha512};

    impl<P: SWCurveConfig> Curve for Projective<P>
    where
        P::ScalarField: Ord,
        P::BaseField: PrimeField,
    {
        type Scalar = P::ScalarField;
        type Base = P::BaseField;

        fn hash_to_curve(person: &str, msg: &[u8]) -> Self {
            let person = person.as_bytes();
            let msg = [person, msg].concat();
            // This is tmp workaround for proper hash_to_curve integration
            let mut count: u64 = 0;
            loop {
                let msg = [msg.clone(), count.to_be_bytes().to_vec()].concat();
                let cand = Sha512::digest(&msg);
                let cand = P::BaseField::from_le_bytes_mod_order(cand.as_slice());
                if let Some(p) = Affine::get_point_from_x_unchecked(cand, true) {
                    return p.mul_by_cofactor().into();
                }
                count += 1;
            }
        }
        fn generator() -> Self {
            P::GENERATOR.into()
        }
        fn to_bytes(&self) -> Vec<u8> {
            let mut bytes = Vec::new();
            self.serialize_compressed(&mut bytes).unwrap();
            bytes
        }
        fn b() -> BigUint {
            P::COEFF_B.uint()
        }
        fn rand(rng: &mut impl RngCore) -> Self {
            <Self as UniformRand>::rand(rng)
        }
        fn identity() -> Self {
            Affine::<P>::identity().into()
        }
        fn coords(&self) -> Point<Self::Base> {
            let affine = self.into_affine();
            let x = affine.x;
            let y = affine.y;
            Point::new(x, y)
        }
        fn from_coords(x: &Self::Base, y: &Self::Base) -> Option<Self> {
            let point = Affine::<P>::new(*x, *y);
            point.is_on_curve().then_some(point.into())
        }
        fn double(&self) -> Self {
            <Self as ark_ec::Group>::double(self)
        }
    }
}
