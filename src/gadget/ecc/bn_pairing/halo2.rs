use super::{e12::E12, e2::E2, e6::E6, witness::BNPairing};
use crate::{
    gadget::{
        big_field::VarBig,
        ecc::{Coordinates, Point},
    },
    Error, Value,
};
use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::halo2curves::bn256::{
    Fq, Fq12, Fq2, Fq6, G1Affine, G2Affine, FROBENIUS_COEFF_FQ6_C1,
};
use halo2_proofs::{arithmetic::Field as _, halo2curves::ff_ext::quadratic::QuadSparseMul};
use itertools::Itertools;
use num_bigint::BigUint;

pub struct Halo2BNPairing;

impl From<&E2<Fq>> for Fq2 {
    fn from(e: &E2<Fq>) -> Self {
        Fq2::new(e.e0, e.e1)
    }
}

impl From<&E6<Fq>> for Fq6 {
    fn from(e: &E6<Fq>) -> Self {
        Fq6::new((&e.e0).into(), (&e.e1).into(), (&e.e2).into())
    }
}

impl From<&E12<Fq>> for Fq12 {
    fn from(e: &E12<Fq>) -> Self {
        Fq12::new((&e.e0).into(), (&e.e1).into())
    }
}

impl From<&E2<BigUint>> for Fq2 {
    fn from(e: &E2<BigUint>) -> Self {
        use crate::Field;
        Fq2::new(Fq::from_uint(&e.e0).unwrap(), Fq::from_uint(&e.e1).unwrap())
    }
}

impl From<&E6<BigUint>> for Fq6 {
    fn from(e: &E6<BigUint>) -> Self {
        Fq6::new((&e.e0).into(), (&e.e1).into(), (&e.e2).into())
    }
}

impl From<&E12<BigUint>> for Fq12 {
    fn from(e: &E12<BigUint>) -> Self {
        Fq12::new((&e.e0).into(), (&e.e1).into())
    }
}

impl From<&Fq2> for E2<BigUint> {
    fn from(e: &Fq2) -> Self {
        use crate::Field;
        E2::new(e.c0().uint(), e.c1().uint())
    }
}

impl From<&Fq6> for E6<BigUint> {
    fn from(e: &Fq6) -> Self {
        E6::new((e.c0()).into(), (e.c1()).into(), (e.c2()).into())
    }
}

impl From<&Fq12> for E12<BigUint> {
    fn from(e: &Fq12) -> Self {
        E12::new((e.c0()).into(), (e.c1()).into())
    }
}

impl From<&Point<E2<BigUint>>> for G2Affine {
    fn from(point: &Point<E2<BigUint>>) -> Self {
        G2Affine::from_xy(point.x().into(), point.y().into()).unwrap()
    }
}

impl From<&G1Affine> for Point<BigUint> {
    fn from(point: &G1Affine) -> Self {
        use crate::Field;
        Point::new(point.x.uint(), point.y.uint())
    }
}

impl From<&G2Affine> for Point<E2<BigUint>> {
    fn from(point: &G2Affine) -> Self {
        Point::new((&point.x).into(), (&point.y).into())
    }
}

impl From<&Point<BigUint>> for G1Affine {
    fn from(point: &Point<BigUint>) -> Self {
        use crate::Field;
        G1Affine::from_xy(
            Fq::from_uint(&point.x).unwrap(),
            Fq::from_uint(&point.y).unwrap(),
        )
        .unwrap()
    }
}

const XIC0: Fq = Fq::from_raw([
    0xdc54014671a0135a,
    0xdbaae0eda9c95998,
    0xdc5ec698b6e2f9b9,
    0x063cf305489af5dc,
]);
const XIC1: Fq = Fq::from_raw([
    0x82d37f632623b0e3,
    0x21807dc98fa25bd2,
    0x0704b5a7ec796f2b,
    0x07c03cbcac41049a,
]);
const XI: Fq2 = Fq2::new(XIC0, XIC1);

impl BNPairing for Halo2BNPairing {
    fn double(acc: &mut Point<E2<BigUint>>) -> (E2<BigUint>, E2<BigUint>) {
        let mut acc_inner: G2Affine = (&acc.clone()).into();
        let G2Affine { x: t_x, y: t_y } = acc_inner;
        let lambda: Fq2 = double(&mut acc_inner);
        let coeff = lambda * t_x - t_y;
        acc.x = (&acc_inner.x).into();
        acc.y = (&acc_inner.y).into();
        ((&lambda).into(), (&coeff).into())
    }

    fn add(
        acc: &mut Point<E2<BigUint>>,
        p: &Point<E2<BigUint>>,
        neg: bool,
    ) -> (E2<BigUint>, E2<BigUint>) {
        let mut acc_inner: G2Affine = (&acc.clone()).into();
        let G2Affine { x: t_x, y: t_y } = acc_inner;
        let lambda = add(&mut acc_inner, &p.into(), neg);
        let coeff = lambda * t_x - t_y;
        acc.x = (&acc_inner.x).into();
        acc.y = (&acc_inner.y).into();
        ((&lambda).into(), (&coeff).into())
    }

    fn w1() -> E12<BigUint> {
        (&w1()).into()
    }

    fn w2() -> E12<BigUint> {
        (&w2()).into()
    }

    fn e12_inverse<N: crate::Field>(e: &E12<VarBig<N>>) -> Result<Value<E12<BigUint>>, Error> {
        e.value().maybe(|e| {
            let e: Fq12 = e.into();
            let inv: Option<Fq12> = e.invert().into();
            inv.map(|inv| (&inv).into())
        })
    }

    fn final_exp_witness(
        p1: &[Point<BigUint>],
        p2: &[Point<E2<BigUint>>],
    ) -> (E12<BigUint>, usize) {
        assert_eq!(p1.len(), p2.len());
        let p1 = p1.iter().map(Into::into).collect_vec();
        let p2 = p2.iter().map(Into::into).collect_vec();
        let f = miller_loop(p1, p2);

        // TODO: box with optional sanity check
        {
            use halo2_proofs::arithmetic::Field;
            use num_traits::Num;

            // naive final exp
            let h = BigUint::from_str_radix(
                "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47",
                16,
            )
            .unwrap();
            let h = h.pow(12) - 1usize;

            let r = &BigUint::from_str_radix(
                "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001",
                16,
            )
            .unwrap();
            let h = h / r;
            assert_eq!(f.pow(h.to_u64_digits()), Fq12::one());
        }

        let c0 = rth_root(&f);
        let c1 = mth_root(&c0);
        let (c, u) = cube_root_with_shift(&c1);

        ((&c).into(), u)
    }
}

pub(crate) fn add(acc: &mut G2Affine, p2: &G2Affine, neg: bool) -> Fq2 {
    let t0 = if neg { acc.y + p2.y } else { acc.y - p2.y };
    let t1 = (acc.x - p2.x).invert().unwrap();
    let lambda = t0 * t1;
    let x3 = lambda.square() - acc.x - p2.x;
    let y3 = lambda * (acc.x - x3) - acc.y;
    acc.x = x3;
    acc.y = y3;
    lambda
}

fn eval(f: &mut Fq12, lambda: Fq2, p1: &G1Affine, t_x: Fq2, t_y: Fq2) {
    let c1 = Fq2::new(lambda.c0() * p1.x, lambda.c1() * p1.x);
    let t = lambda * t_x - t_y;
    let c3 = Fq2::new(t.c0() * p1.y, t.c1() * p1.y);
    Fq12::mul_by_034(f, &Fq2::one(), &c1, &c3);
}

pub(crate) fn double(acc: &mut G2Affine) -> Fq2 {
    let x2 = acc.x.square();
    let t0 = x2.double() + x2;
    let t1 = acc.y.double().invert().unwrap();
    let lambda = t0 * t1;

    let x3 = lambda.square() - acc.x.double();

    let y3 = lambda * (acc.x - x3) - acc.y;

    acc.x = x3;
    acc.y = y3;
    lambda
}

fn double_eval(f: &mut Fq12, acc: &mut G2Affine, p1: &G1Affine) {
    let G2Affine { x: t_x, y: t_y } = *acc;
    let lambda = double(acc);
    eval(f, lambda, p1, t_x, t_y);
}

fn add_eval(f: &mut Fq12, acc: &mut G2Affine, p2: &G2Affine, p1: &G1Affine, neg: bool) {
    let G2Affine { x: t_x, y: t_y } = *acc;
    let lambda: Fq2 = add(acc, p2, neg);
    eval(f, lambda, p1, t_x, t_y);
}

// TODO: use halo2curves miller loop once we move to new version of halo2curves
pub(crate) fn miller_loop(
    p1: impl IntoIterator<Item = G1Affine>,
    p2: impl IntoIterator<Item = G2Affine>,
) -> Fq12 {
    use halo2_proofs::halo2curves::group::prime::PrimeCurveAffine;
    let terms = p1
        .into_iter()
        .zip(p2)
        .map(|(p1, p2)| {
            // prepare
            assert!(!bool::from(p1.is_identity()));
            assert!(!bool::from(p2.is_identity()));
            let y = p1.y.invert().unwrap();
            let x = (p1.x * y).neg();
            let p1 = G1Affine { x, y };
            (p1, p2)
        })
        .collect::<Vec<_>>();

    let mut f = Fq12::one();
    let mut acc = terms.iter().map(|(_, q)| *q).collect::<Vec<_>>();

    super::SIX_U_PLUS_2_NAF
        .iter()
        .rev()
        .skip(1)
        .enumerate()
        .for_each(|(i, x)| {
            (i != 0).then(|| f.square_assign());

            terms
                .iter()
                .zip(acc.iter_mut())
                .for_each(|((g1, _), acc)| double_eval(&mut f, acc, g1));

            #[allow(clippy::single_match)]
            match x {
                val @ (1 | -1) => {
                    terms
                        .iter()
                        .zip(acc.iter_mut())
                        .for_each(|((g1, q), r)| add_eval(&mut f, r, q, g1, val.is_negative()));
                }

                _ => {}
            }
        });

    terms.iter().zip(acc.iter_mut()).for_each(|((p, q), acc)| {
        let mut q1: G2Affine = *q;
        q1.x.conjugate();
        q1.x.mul_assign(&FROBENIUS_COEFF_FQ6_C1[1]);
        q1.y.conjugate();
        q1.y.mul_assign(&XI);
        add_eval(&mut f, acc, &q1, p, false);
    });

    terms.iter().zip(acc.iter_mut()).for_each(|((p, q), acc)| {
        let mut minusq2: G2Affine = *q;
        minusq2.x.mul_assign(&FROBENIUS_COEFF_FQ6_C1[2]);
        add_eval(&mut f, acc, &minusq2, p, false);
    });

    f
}

pub(crate) fn w1() -> Fq12 {
    // TODO: make constant

    use halo2_proofs::halo2curves::ff::PrimeField;

    let e0 = Fq6::new(
        Fq2::zero(),
        Fq2::zero(),
        Fq2::new(
            Fq::from_str_vartime(
                "2268774813928168705714769340309076012973838184912660903371022264081608589547",
            )
            .unwrap(),
            Fq::from_str_vartime(
                "4505553186665064976568408494606738900088290417616355650737309862368100888609",
            )
            .unwrap(),
        ),
    );
    let e1 = Fq6::zero();
    Fq12::new(e0, e1)
}

pub(crate) fn w2() -> Fq12 {
    // TODO: make constant

    w1() * w1()
}

pub fn rth_root(e: &Fq12) -> Fq12 {
    // TODO: optimize exp
    const R_PRIME: [u64; 44] = [
        0xa11b194379daaca1,
        0xa5f0d2dcad831751,
        0x2b410d5c2e47c1b4,
        0x384a4274ed212efc,
        0x70aac1f263098d89,
        0x00f5fd95b7c6784e,
        0x7ebfe5d9a66b49bb,
        0x1c4d0568f9a146bb,
        0xc647b55ab5455a1f,
        0x315372b248a33b03,
        0xaa284fca9651ce25,
        0x1f401dc214ffb6d3,
        0x65cfacd3e5294c64,
        0xcce86cb5c9a967d9,
        0xd457e4e53e766cdf,
        0xc3c33ad27ef8286d,
        0xb0c4571cbda9e9b9,
        0x026024e519498470,
        0xb517826e8d0a7ea3,
        0xfe0b42fd3f9e4cb6,
        0xdf7db6f0f880457b,
        0x182418ed6397d5da,
        0x4dbb3c5f77a5e53d,
        0xd8252918fdce3f1e,
        0xfd9bd55b098443f5,
        0xf8a2e6743a1e2509,
        0xfe45c6ba38a2a7d2,
        0x379e03a9a5e228c5,
        0xc190b44c4eaa05ef,
        0xe326d9499c2238ca,
        0x068e0b9719edade8,
        0x51acfb2c2b91395f,
        0x23575e4b046e4551,
        0x28206b1dd3e111f2,
        0xee7b16d7001a28fd,
        0xcc9f2cef8aa8b968,
        0x82165fad421d6efa,
        0xe0d2744ba5f78583,
        0xa5fa4275e36247c2,
        0x847f3dae4767238b,
        0x4c2fca934b0d67ba,
        0xf17857b96814f37b,
        0x79815b691a6a294e,
        0x0000002a71a42aee,
    ];
    use halo2_proofs::arithmetic::Field;
    e.pow(R_PRIME)
}

pub fn mth_root(e: &Fq12) -> Fq12 {
    // TODO: optimize exp
    const M_PRIME_PRIME: [u64; 44] = [
        0xf7721c7aff2f56b7,
        0xa41c1525e62392af,
        0xf08969a9108c577f,
        0x843248b70bc58b9b,
        0x072d7a403a1e679c,
        0x88c5e5a473bf4dc0,
        0x51c8b0e8579cc523,
        0xb459b999d3ac8a7d,
        0x18fa924d8034a528,
        0xc55e1e6afd4f17a6,
        0xb3667969b57a1a59,
        0x38188d68645ec977,
        0x4ce226be79e0093e,
        0x93f8674a5444d2ec,
        0x111b573624f772f3,
        0x349070d501f354a4,
        0xff1e01c9b766a835,
        0x4d90962b1fc6ee8f,
        0xb6fe4cd038239172,
        0xe82a55d5a62a0447,
        0x2ddd7fea7f5d2359,
        0xeebee1afc60f5209,
        0x8a10190cff16e8e4,
        0x9d001574cb7631fa,
        0x0d0f5585b4ca70cc,
        0x496f56776b19ac89,
        0x91f3035f8757e549,
        0xfd3d06751c3e97a3,
        0xe51a66ac9a83c506,
        0xdf0ea52e1e84aa13,
        0xce20f6fcdca29467,
        0x8591195a1879549f,
        0x5261846036719b2e,
        0xdec7495884c546a9,
        0x2d6eb7558005a1ee,
        0xe534278298cad674,
        0xa29b3e0abf45fbcb,
        0x0bd4341f0e9cc796,
        0xf544c6143b686a58,
        0x5d32122cd9a4aa34,
        0xadc0eee93555b6d4,
        0x715424f40cb25186,
        0x8dd1549b7e60deaa,
        0x0000000186f601e0,
    ];
    use halo2_proofs::arithmetic::Field;
    e.pow(M_PRIME_PRIME)
}

pub(crate) fn cube_root_with_shift(e: &Fq12) -> (Fq12, usize) {
    if !is_cube_nonresidue(e) {
        return (cube_root(e).unwrap(), 0);
    }

    let a = e * w1();
    if !is_cube_nonresidue(&a) {
        return (cube_root(&a).unwrap(), 1);
    }

    let a = e * w2();
    if !is_cube_nonresidue(&a) {
        return (cube_root(&a).unwrap(), 2);
    }

    unreachable!();
}

// TODO: optimize exp
const CUBE_NON_RES_EXP: [u64; 48] = [
    0xeb46f64643825060,
    0xc09504ce57838ff3,
    0xb6973b1dfda111a7,
    0x9e6a6b1d46fc408c,
    0x745bdaf039c199f6,
    0xe9f65a41395df713,
    0x4dcd3d267739953c,
    0x9f49699c7d2e3b27,
    0xb189f37c0ecd514e,
    0x55aa926463b3f1ad,
    0x6030fad438f67304,
    0x1dc6e7821edb8a5c,
    0x3fabe2a396c821ee,
    0xce442caa65704817,
    0xac5266c00ed4ded7,
    0x53aa9ef14c0ae51f,
    0x133df7ebbc224e97,
    0x88ce9faea263de92,
    0x8c4be6bdd2b88017,
    0x628d5a19e9c247d9,
    0xa93bf3094d3d5518,
    0x3939f77b19cd8e05,
    0x3c85c4759d907006,
    0xf47559371ceb7cb4,
    0x9868d7443cc60fe8,
    0x591589f02cf8ecb7,
    0x680fa342f7100bba,
    0xb44b431aae371e85,
    0x99625bea8196289d,
    0xa38d36e079b35749,
    0x08d38b7277eb44ec,
    0xb5de835af494b061,
    0x370bd1df6206ad8e,
    0xf755226d1fb5139f,
    0xedafa93168993756,
    0x5b43e8559e471ed9,
    0xe84ed08d6375382d,
    0x9b99a5c06b47a88a,
    0x19e45304da068978,
    0x12aff3b863cdce2f,
    0xb0178e622c3aaf92,
    0x19e6b3b6373de8df,
    0xeb4cec3eff8e12f1,
    0xc3fc152a73114859,
    0xd516d062f8015f36,
    0x6440dd3153897c68,
    0x73924a5d67a5d259,
    0x00000002fae42e49,
];

// TODO: optimize exp
const CUBE_CLEAR_EXP: [u64; 48] = [
    0x7102a0d331e861cb,
    0x1a187b6ff0473e38,
    0xcddfacdb2f51d13f,
    0x483cd48f4e7b1ed5,
    0xd4e6f5255778f2bd,
    0x83ecae026a6bc6c7,
    0x911a907caf15187d,
    0xe9747f2bb8c8d2c8,
    0x069354deab370302,
    0x61fcd603b7d741d7,
    0xcaac7b1157716c8e,
    0xb540417698d8b945,
    0x6aa78d2280d80141,
    0x4a028665203390e4,
    0x6eadb7f42679a970,
    0x586e9d9728be087c,
    0xedbfecbce10ac08a,
    0x1807a7196e4f8cfb,
    0xdf452e78ceea638f,
    0xb7cc58aba05c8766,
    0xb0ef41e3e66a915f,
    0x3b02259c43537709,
    0x31a623b881185000,
    0x4b6ca47d4cec46fd,
    0xd63cc59a3b23c7b3,
    0x7513c2bd0b25a9f3,
    0xdded9dc01c1d09ea,
    0xcdc9e60a783aee2a,
    0x9d62752e9c80d218,
    0x944799bc7649033b,
    0xed5d2b1733d94e67,
    0x19b2e86baa3e6558,
    0xe5982437ae4c1964,
    0xffadd1de1d9e6905,
    0x253f6514cafc3174,
    0x58b6a9ca483b85e2,
    0xe2ad95f2460dd2ac,
    0x8a80f32d0d746e89,
    0xe483b739118e76de,
    0x4c8b41ea6282e1b5,
    0x81c7fbcabf448b3e,
    0x4ccfa7d757611b96,
    0x2528c66125e8d14b,
    0x6612d16063139a62,
    0xd87c1aae55098844,
    0x628724a303180e16,
    0x33b015b79b8ae1dd,
    0x000000001c41570c,
];

pub(crate) fn cube_root(e: &Fq12) -> Option<Fq12> {
    use halo2_proofs::arithmetic::Field;

    let w = w1();

    let mut a = e.pow(CUBE_CLEAR_EXP);

    for _ in 0..27 {
        if (a * a * a) == *e {
            return Some(a);
        }
        a *= w;
    }

    None
}

fn is_cube_nonresidue(e: &Fq12) -> bool {
    use halo2_proofs::arithmetic::Field;
    e.pow(CUBE_NON_RES_EXP) != Fq12::one()
}

#[cfg(test)]
pub(crate) mod test {
    use super::Halo2BNPairing;
    use crate::gadget::big_field::crt::CrtGadget;
    use crate::gadget::ecc::bn_pairing::BNPairingGadget;
    use crate::gadget::ecc::ecc_base_field::BaseFieldEccGadget;
    use crate::gadget::ecc::test::base_field_ecc;
    use crate::gadget::ecc::{EccGadget, Point};
    use crate::ir::ac::{AbstractCircuit, AbstractConfig};
    use crate::utils::test::xor_rng;
    use crate::Field;
    use halo2_proofs::arithmetic::CurveAffine;
    use halo2_proofs::halo2curves::bn256::{
        Fq, Fq2, Fr, G1Affine, G2Affine, FROBENIUS_COEFF_FQ12_C1, FROBENIUS_COEFF_FQ6_C1,
        FROBENIUS_COEFF_FQ6_C2, G1,
    };
    use halo2_proofs::halo2curves::group::prime::PrimeCurveAffine;
    use halo2_proofs::halo2curves::group::Curve;
    use itertools::Itertools;

    fn new_pairing_gadget<N: Field>(
        base_field: &CrtGadget<N>,
    ) -> BNPairingGadget<N, Halo2BNPairing> {
        let frobenius61 = FROBENIUS_COEFF_FQ6_C1
            .as_ref()
            .iter()
            .map(Into::into)
            .collect_vec();
        let frobenius62 = FROBENIUS_COEFF_FQ6_C2
            .as_ref()
            .iter()
            .map(Into::into)
            .collect_vec();
        let frobenius12 = FROBENIUS_COEFF_FQ12_C1
            .as_ref()
            .iter()
            .map(Into::into)
            .collect_vec();

        let xi = (&super::XI).into();
        let b2 = (&G2Affine::b()).into();

        const U0: Fq = Fq::from_raw([
            0x99e39557176f553d,
            0xb78cc310c2c3330c,
            0x4c0bec3cf559b143,
            0x2fb347984f7911f7,
        ]);
        const U1: Fq = Fq::from_raw([
            0x1665d51c640fcba2,
            0x32ae2a1d0b7c9dce,
            0x4ba4cc8bd75a0794,
            0x16c9e55061ebae20,
        ]);
        let u = Fq2::new(U0, U1);
        const V0: Fq = Fq::from_raw([
            0xdc54014671a0135a,
            0xdbaae0eda9c95998,
            0xdc5ec698b6e2f9b9,
            0x063cf305489af5dc,
        ]);
        const V1: Fq = Fq::from_raw([
            0x82d37f632623b0e3,
            0x21807dc98fa25bd2,
            0x0704b5a7ec796f2b,
            0x07c03cbcac41049a,
        ]);
        let v = Fq2::new(V0, V1);

        BNPairingGadget::<N, Halo2BNPairing>::new(
            base_field,
            frobenius61.try_into().unwrap(),
            frobenius62.try_into().unwrap(),
            frobenius12.try_into().unwrap(),
            (&u).into(),
            (&v).into(),
            xi,
            b2,
        )
    }

    pub(crate) fn pairing_test(
        ac: &mut AbstractCircuit<Fr>,
        rng: &mut impl rand::RngCore,
        n: usize,
        n_fix: usize,
    ) {
        let g1 = G1Affine::generator();
        let g2 = G2Affine::generator();
        let scalars = (0..n - 1)
            .map(|_| (Fr::rand(rng), Fr::rand(rng)))
            .collect::<Vec<_>>();
        let last = scalars
            .iter()
            .fold(Fr::zero(), |acc, (u0, u1)| acc + u0 * u1);
        let (mut p1, mut p2): (Vec<_>, Vec<_>) = scalars
            .iter()
            .map(|(a, b)| ((g1 * a).to_affine(), (g2 * b).to_affine()))
            .unzip();
        p1.push(-g1);
        p2.push((g2 * last).into());

        let ecc: BaseFieldEccGadget<G1> = base_field_ecc(15, 90);
        let crt = ecc.base_field_crt();
        let pairing = new_pairing_gadget(crt);

        {
            let p1 = p1
                .iter()
                .map(|p| ecc.assign_point(ac, &p.to_curve().into()).unwrap())
                .collect_vec();

            let p2 = p2
                .iter()
                .map(|p| {
                    let p: Point<_> = p.into();
                    pairing.assign_g2(ac, &p.into()).unwrap()
                })
                .collect_vec();
            pairing.pairing_check(ac, &p1, &p2).unwrap();
        }

        {
            let p1 = p1
                .iter()
                .map(|p| ecc.assign_point(ac, &p.to_curve().into()).unwrap())
                .collect_vec();

            let (p1_var, p1_fix) = p1.split_at(n_fix);
            let (p2_var, p2_fix) = p2.split_at(n_fix);

            let p2_var = p2_var
                .iter()
                .map(|p| {
                    let p: Point<_> = p.into();
                    pairing.assign_g2(ac, &p.into()).unwrap()
                })
                .collect_vec();
            let p2_fix = p2_fix.iter().map(Into::into).collect_vec();
            pairing
                .pairing_check_mixed(ac, p1_var, &p2_var, p1_fix, &p2_fix)
                .unwrap();
        }
        ac.print_info(false);
    }

    #[test]
    fn test_pairing() {
        let cfg = AbstractConfig::default();
        let ac = &mut AbstractCircuit::<Fr>::new(cfg);
        let rng = &mut xor_rng();
        pairing_test(ac, rng, 4, 3);
    }
}
