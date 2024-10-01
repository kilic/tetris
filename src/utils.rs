use itertools::izip;
use itertools::Itertools;
use num_bigint::BigInt;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::borrow::Borrow;

pub fn transpose<'a, N>(chunk: &[&'a [N]]) -> Vec<Vec<&'a N>> {
    let n_columns = chunk.len();
    let n_rows = chunk.first().unwrap().len();
    assert!(chunk.iter().skip(1).all(|c| c.len() == n_rows));
    (0..n_rows)
        .map(|i| (0..n_columns).map(|j| &chunk[j][i]).collect())
        .collect()
}

pub fn product<'a, L, R, Out>(a: &'a [L], b: &'a [R]) -> Vec<Vec<Out>>
where
    &'a L: std::ops::Mul<&'a R, Output = Out>,
{
    let mut wide: Vec<Vec<Out>> = vec![];
    for (i, a) in a.iter().enumerate() {
        for (j, b) in b.iter().enumerate() {
            if wide.len() <= i + j {
                wide.push(vec![]);
            }
            wide.get_mut(i + j).unwrap().push(a * b);
        }
    }
    wide
}

pub fn decompose_uint(e: &BigUint, n_limbs: usize, limb_size: usize) -> Vec<BigUint> {
    let mask = &((BigUint::one() << limb_size) - 1usize);
    (0usize..)
        .step_by(limb_size)
        .take(n_limbs)
        .map(|shift| ((e >> shift) & mask))
        .collect_vec()
}

pub fn decompose_int(e: &BigInt, n_limbs: usize, limb_size: usize) -> Vec<BigInt> {
    use num_traits::Signed;
    let magnitude = e.magnitude();
    let negate = e.is_negative();
    let limbs = decompose_uint(magnitude, n_limbs, limb_size);
    limbs
        .iter()
        .map(|limb| {
            let limb: BigInt = limb.clone().into();
            if negate {
                -limb
            } else {
                limb
            }
        })
        .collect()
}

pub fn select<T>(bool: bool, a0: T, a1: T) -> T {
    if bool {
        a0
    } else {
        a1
    }
}

pub fn compose_uint<I>(input: I, limb_size: usize) -> BigUint
where
    I: IntoIterator,
    I::Item: Borrow<BigUint>,
    I::IntoIter: DoubleEndedIterator,
{
    input.into_iter().rev().fold(BigUint::zero(), |acc, val| {
        (acc << limb_size) + val.borrow()
    })
}

pub fn compose_int<I>(input: I, limb_size: usize) -> BigInt
where
    I: IntoIterator,
    I::Item: Borrow<BigInt>,
    I::IntoIter: DoubleEndedIterator,
{
    input
        .into_iter()
        .rev()
        .fold(BigInt::zero(), |acc, val| (acc << limb_size) + val.borrow())
}

fn mask(n: usize) -> BigUint {
    (BigUint::one() << n) - 1usize
}

pub fn decompose_uint_nonuniform(e: &BigUint, sizes: &[usize]) -> Vec<BigUint> {
    sizes.iter().for_each(|size| assert_ne!(size, &0));
    let mut shift = 0;
    sizes
        .iter()
        .map(|size| {
            let mask = mask(*size);
            let limb = (e >> shift) & mask;
            shift += size;
            limb
        })
        .collect_vec()
}

pub fn compose_uint_nonuniform(limbs: &[BigUint], sizes: &[usize]) -> BigUint {
    assert_eq!(limbs.len(), sizes.len());
    sizes.iter().for_each(|size| assert_ne!(size, &0));

    izip!(limbs, sizes)
        .rev()
        .fold(BigUint::zero(), |acc, (val, size)| (acc << size) + val)
}

pub fn log2(x: usize) -> u32 {
    if x == 0 {
        0
    } else if x.is_power_of_two() {
        1usize.leading_zeros() - x.leading_zeros()
    } else {
        0usize.leading_zeros() - x.leading_zeros()
    }
}

#[cfg(test)]
pub(crate) mod test {

    use itertools::Itertools;
    use num_bigint::RandBigInt;
    use rand::Rng;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    #[cfg(test)]
    pub(crate) fn xor_rng() -> XorShiftRng {
        XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ])
    }

    #[test]
    fn test_numbigint_compose_roundtrip() {
        let rng = &mut xor_rng();

        for n_limbs in 1..20usize {
            for limb_size in 1..20usize {
                let max_size = n_limbs * limb_size;

                let a0 = rng.gen_biguint(max_size as u64);
                let limbs = super::decompose_uint(&a0, n_limbs, limb_size);
                let a1 = super::compose_uint(&limbs, limb_size);
                assert_eq!(a0, a1);

                let a0 = rng.gen_bigint(max_size as u64);
                let limbs = super::decompose_int(&a0, n_limbs, limb_size);
                let a1 = super::compose_int(&limbs, limb_size);
                assert_eq!(a0, a1);
            }
        }
    }

    #[test]
    fn test_numbigint_compose_nonuniform_roundtrip() {
        let rng = &mut xor_rng();
        for n_limbs in 1..20usize {
            let sizes: Vec<usize> = (0..n_limbs).map(|_| rng.gen_range(1..10)).collect_vec();
            let number_size = sizes.iter().sum::<usize>();
            let a0 = rng.gen_biguint(number_size as u64);
            let limbs = super::decompose_uint_nonuniform(&a0, &sizes);
            let a1 = super::compose_uint_nonuniform(&limbs, &sizes);
            assert_eq!(a0, a1);
        }
    }

    #[test]
    #[cfg(any(feature = "arkworks", feature = "halo2"))]
    fn test_field_compose_nonuniform() {
        use crate::Field;
        #[cfg(feature = "arkworks")]
        use ark_bn254::Fr;
        #[cfg(feature = "halo2")]
        use halo2_proofs::halo2curves::bn256::Fr;

        let rng = &mut xor_rng();
        for _ in 0..1000 {
            for n_limbs in 1..20usize {
                let sizes: Vec<usize> = (0..n_limbs).map(|_| rng.gen_range(1..10)).collect_vec();
                let number_size = sizes.iter().sum::<usize>();
                let a0 = rng.gen_biguint(number_size as u64);
                let a0 = Fr::from_uint(&a0).unwrap();
                let limbs = a0.decompose_nonuniform(&sizes);
                let a1 = Fr::compose_nonuniform(&limbs, &sizes);
                assert_eq!(a0, a1);
            }
        }
    }
}
