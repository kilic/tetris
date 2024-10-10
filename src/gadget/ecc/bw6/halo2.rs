use super::{e3::E3, e6::E6, witness::Bw6Pairing, LOOP_1_NAF, LOOP_2_NAF};
use crate::{
    gadget::{big_field::VarBig, ecc::Point},
    Error, Field, Value,
};
use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::halo2curves::ff::WithSmallOrderMulGroup;
use halo2_proofs::halo2curves::{
    bw6::{Fq, Fq3, Fq6, G1Affine, G2Affine},
    ff_ext::ExtField,
};
use halo2_proofs::{arithmetic::Field as _, halo2curves::ff_ext::quadratic::QuadSparseMul};
use itertools::Itertools;
use num_bigint::BigUint;
use num_traits::Num;
use std::ops::Neg;

pub struct Halo2Bw6Pairing;

impl From<&Fq3> for E3<BigUint> {
    fn from(e: &Fq3) -> Self {
        use crate::Field;
        E3::new(e.c0().uint(), e.c1().uint(), e.c2().uint())
    }
}

impl From<&Fq6> for E6<BigUint> {
    fn from(e: &Fq6) -> Self {
        E6::new((e.c0()).into(), (e.c1()).into())
    }
}

impl From<&E3<Fq>> for Fq3 {
    fn from(e: &E3<Fq>) -> Self {
        Fq3::new(e.e0, e.e1, e.e2)
    }
}

impl From<&E6<Fq>> for Fq6 {
    fn from(e: &E6<Fq>) -> Self {
        Fq6::new((&e.e0).into(), (&e.e1).into())
    }
}

impl From<&E3<BigUint>> for Fq3 {
    fn from(e: &E3<BigUint>) -> Self {
        Fq3::new(
            Fq::from_uint(&e.e0).unwrap(),
            Fq::from_uint(&e.e1).unwrap(),
            Fq::from_uint(&e.e2).unwrap(),
        )
    }
}

impl From<&E6<BigUint>> for Fq6 {
    fn from(e: &E6<BigUint>) -> Self {
        Fq6::new((&e.e0).into(), (&e.e1).into())
    }
}

impl From<&G1Affine> for Point<BigUint> {
    fn from(point: &G1Affine) -> Self {
        use crate::Field;
        Point::new(point.x.uint(), point.y.uint())
    }
}

impl From<&G2Affine> for Point<BigUint> {
    fn from(point: &G2Affine) -> Self {
        use crate::Field;
        Point::new(point.x.uint(), point.y.uint())
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

impl From<&Point<BigUint>> for G2Affine {
    fn from(point: &Point<BigUint>) -> Self {
        use crate::Field;
        G2Affine::from_xy(
            Fq::from_uint(&point.x).unwrap(),
            Fq::from_uint(&point.y).unwrap(),
        )
        .unwrap()
    }
}

fn endo_g2(p: &G2Affine) -> G2Affine {
    G2Affine {
        x: p.x * Fq::ZETA,
        y: -p.y,
    }
}

impl Bw6Pairing for Halo2Bw6Pairing {
    fn final_exp_witness(p1: &[Point<BigUint>], p2: &[Point<BigUint>]) -> E6<BigUint> {
        assert_eq!(p1.len(), p2.len());
        let p1 = p1.iter().map(Into::into).collect_vec();
        let p2 = p2.iter().map(Into::into).collect_vec();
        let f = miller_loop(&p1, &p2, &Fq6::one());
        let c = r_inv(&f);
        let c = m_inv(&c);
        // {
        //     let is_one = miller_loop(&p1, &p2, &c);
        //     assert_eq!(is_one, Fq6::one());
        // }
        (&c).into()
    }

    fn double(acc: &mut Point<BigUint>) -> (BigUint, BigUint) {
        let mut acc_inner: G2Affine = (&acc.clone()).into();
        let G2Affine { x: t_x, y: t_y } = acc_inner;
        let lambda: Fq = dbl(&mut acc_inner);
        let nu = lambda * t_x - t_y;
        acc.x = acc_inner.x.uint();
        acc.y = acc_inner.y.uint();
        (lambda.uint(), nu.uint())
    }

    fn add(
        acc: &mut Point<BigUint>,
        p: &Point<BigUint>,
        neg: bool,
        endo: bool,
    ) -> (BigUint, BigUint) {
        let mut acc_inner: G2Affine = (&acc.clone()).into();
        let G2Affine { x: t_x, y: t_y } = acc_inner;
        let lambda = add(&mut acc_inner, &p.into(), neg, endo);
        let nu = lambda * t_x - t_y;
        acc.x = acc_inner.x.uint();
        acc.y = acc_inner.y.uint();
        (lambda.uint(), nu.uint())
    }

    fn e6_inverse<N: crate::Field>(e: &E6<VarBig<N>>) -> Result<Value<E6<BigUint>>, Error> {
        e.value().maybe(|e| {
            let e: Fq6 = e.into();
            let inv: Option<Fq6> = e.invert().into();
            inv.map(|inv| (&inv).into())
        })
    }

    fn endo(acc: &[Point<BigUint>]) -> Vec<Point<BigUint>> {
        acc.iter()
            .map(|p| (&endo_g2(&p.into())).into())
            .collect_vec()
    }
}

fn eval(f: &mut Fq6, u0: &Fq, u1: &Fq) {
    Fq6::mul_by_014(f, u0, u1, &Fq::one());
}

fn add(acc: &mut G2Affine, q: &G2Affine, neg: bool, end: bool) -> Fq {
    let q = if end { endo_g2(q) } else { *q };
    let q = if neg { q.neg() } else { q };
    let t0 = acc.y - q.y;
    let t1 = acc.x - q.x;
    let lmd = t1.invert().unwrap() * t0;
    let x = lmd.square() - acc.x - q.x;
    let y = lmd * (acc.x - x) - acc.y;
    *acc = G2Affine::from_xy(x, y).unwrap();
    lmd
}

fn add_eval(f: &mut Fq6, acc: &mut G2Affine, p2: &G2Affine, p1: &G1Affine, neg: bool, endo: bool) {
    let rx = acc.x;
    let ry = acc.y;
    let lmd = add(acc, p2, neg, endo);
    let nu = lmd * rx - ry;
    let u1 = lmd * p1.x;
    let u0 = nu * p1.y;
    eval(f, &u0, &u1);
}

fn dbl(acc: &mut G2Affine) -> Fq {
    let xx = acc.x.square();
    let xx3 = xx + xx + xx;
    let yy2 = acc.y + acc.y;
    let iyy2 = yy2.invert().unwrap();
    let lmd = xx3 * iyy2;
    let x = lmd.square() - acc.x - acc.x;
    let y = lmd * (acc.x - x) - acc.y;
    *acc = G2Affine::from_xy(x, y).unwrap();
    lmd
}

fn dbl_eval(f: &mut Fq6, acc: &mut G2Affine, p: &G1Affine) {
    let rx = acc.x;
    let ry = acc.y;
    let lmd = dbl(acc);
    let nu = lmd * rx - ry;
    let u1 = lmd * p.x;
    let u0 = nu * p.y;
    eval(f, &u0, &u1);
}

pub fn miller_loop(p1: &[G1Affine], p2: &[G2Affine], c: &Fq6) -> Fq6 {
    // Follows 6th equation at https://hackmd.io/@gnark/BW6-761-changes

    let c_inv = c.invert().unwrap();
    let mut cq = *c;
    cq.frobenius_map(1);
    let mut cq_inv = c_inv;
    cq_inv.frobenius_map(1);

    let p1 = p1
        .iter()
        .map(|p| {
            let y = p.y.invert().unwrap();
            let x = (p.x * y).neg();
            G1Affine { x, y }
        })
        .collect::<Vec<_>>();

    let mut f = cq_inv;
    let mut acc = p2.iter().map(endo_g2).collect::<Vec<_>>();

    for (x2, x1) in LOOP_2_NAF
        .iter()
        .skip(1)
        .rev()
        .skip(1)
        .zip(LOOP_1_NAF.iter().skip(1).rev().skip(1))
    {
        let x = x2 * 3 + x1;

        f.square_assign();

        p1.iter()
            .zip(acc.iter_mut())
            .for_each(|(p, acc)| dbl_eval(&mut f, acc, p));

        match x {
            -3 => {
                f *= &cq;

                p1.iter()
                    .zip(p2.iter())
                    .zip(acc.iter_mut())
                    .for_each(|((p1, p2), acc)| add_eval(&mut f, acc, p2, p1, true, true));
            }
            -1 => {
                f *= c;

                p1.iter()
                    .zip(p2)
                    .zip(acc.iter_mut())
                    .for_each(|((p1, p2), acc)| add_eval(&mut f, acc, p2, p1, true, false));
            }
            1 => {
                f *= &c_inv;

                p1.iter()
                    .zip(p2)
                    .zip(acc.iter_mut())
                    .for_each(|((p1, p2), acc)| add_eval(&mut f, acc, p2, p1, false, false));
            }
            3 => {
                f *= &cq_inv;

                p1.iter()
                    .zip(p2.iter())
                    .zip(acc.iter_mut())
                    .for_each(|((p1, p2), acc)| add_eval(&mut f, acc, p2, p1, false, true));
            }
            _ => {}
        }
    }
    f.square_assign();

    p1.iter()
        .zip(acc.iter_mut())
        .for_each(|(p, acc)| dbl_eval(&mut f, acc, p));

    // last round x = -3
    // but acc == p2
    f *= &cq;

    f
}

pub(super) fn r_inv(e: &Fq6) -> Fq6 {
    let r_i = "dd165f72375dd203252eb746be13df990bfd5452b9ce1e01a99fe6ab47de540eef3e192658eee271d9f17174ae23a0680a7e25059aa190b3527f3b4c0dd073c49d1cf0f3922a12134d592226b8bcfd6e9c25dd434d7c7dc9a59f2149eb2d279c4b5b28e70170cbe10dd765feefe5efca4ff8f9ff95efb3af0a54e0dadf422f899df03066586d51310f88c1816d0696b508ca6ad4ba2a18c412b540ed9b68e7d6fd5e9a3bee952e60bc683d04a5efd292ff351bf525467ed4afc6b75d8be1b348ede2b05edb62bbc12648d9634e82ff1c1b14dd384bca77927b701b3774a9f764bb51bdcded75c0b39babf0e68ca0c774970a5550263fd5216431e4292710e4d2d37a489dba4c4cdb36f93d523691204a72c79e1088f77f697df50f5505bd4cc620470e974730a3eaaae6fde70572bf14d98b7c99a03bab03b7a88bd88f94391c54c81b2082bd7695fb4830c7216241a950b7d5359d86fce5ab0ed93c32d8e1d39c16741db5123841a0f87fc256e1bbf887fdbe6335a18717eba7084af7b9fb7a126c5ca8ad6ed44f1505fb8162152f738717a0ad969341043ab138a16f57c287cb810a8b94bdc0631c0d7b80f970d40d5eeb745fafbd16e138afa04ac943668002e132e4e32a4106abeacdf626533f75a52eb5fe5c0fb494a17f1f644c80745fa6493d64f0230e061b5bc3dd0085b251f358c2a051d17cf6c3a571e4517617784e21ef26547136cd9426d9";
    let r_i = BigUint::from_str_radix(r_i, 16).unwrap();
    e.pow(r_i.to_u64_digits())
}

pub(super) fn m_inv(e: &Fq6) -> Fq6 {
    let r_i = "536699dbd98c57931276d1bdc2d5d4515cb10370d6c21cecdb6b351c9a1e40157d00d1b05f69e9d8cb6318edb26fe948ab63764a65f2b285a4fe4757b86ef3215b9966c92781bdbe20101ac0c2d719a16190e6c459167e22d5bc43024c279f1c888df10336c8ab28e3dc39d34027f2fb0f09ef5453c5377a1eaf8620ad036c5d821746ab754f9ba0985ecfb6ac65904ea31971bf28bf0bccde72adb0343abb1a1728fefaab909339bb0763930158bc62245870e3c7e234301cf98db672c498b16fecf0485fc5ba2d9e5dbcfc95c9f487114b4ffcb0a7485f6308a2f37aa1fda35b48d9acec42aa651830a0ccc861240e91691b35688a7fcf1ce479a7f49f330d0022323fbc3a67d90c826d462b14f1b44c674fa5ed7cc2acbf9862d3688b907a0da98668273c296c0211e907ca3966092222d8f73f0a3972b9dec1360cfe4f5a20433e4999c229ca39113118115df5ab5a77359e9d1df6c1098e4ee31ac1a45500b7ec78bfadc6dbf5fd15aa34758c8f9c85652c01e3d5c958aa9e4e0230b6bee9dd9c9a541eb7c6057fdb93950f81562ca5215539f563e1f01a19ffdc9b57f46886eef25b28f94de9e48a5c5cd8a98441da20a6b4db888960ca4779e721bd3c5ae14274b4bd12909f749781791f723b7b03b6e4d0d8ea77bf3fbc4fcc0e6b96cd6047131d7c01a1530cadda765e9ecb03009a890b6992bb724cd1aef7fc54a06c0e98cf728fc9c0884ec7";
    let r_i = BigUint::from_str_radix(r_i, 16).unwrap();
    e.pow(r_i.to_u64_digits())
}

#[cfg(test)]
pub(crate) mod test {
    use super::Halo2Bw6Pairing;
    use crate::gadget::big_field::crt::CrtGadget;
    use crate::gadget::ecc::bw6::halo2::{m_inv, miller_loop, r_inv};
    use crate::gadget::ecc::bw6::Bw6PairingGadget;
    use crate::gadget::ecc::ecc_general::GeneralEccGadget;
    use crate::gadget::ecc::EccGadget;
    use crate::halo2::config::{GateConfig, RangeGateConfig};
    use crate::halo2::test::{run_kzg_prover, run_mock_prover, Synth};
    use crate::ir::ac::{AbstractCircuit, AbstractConfig};
    use crate::utils::test::xor_rng;
    use crate::Field;
    use halo2_proofs::arithmetic::Field as _;
    use halo2_proofs::halo2curves::bw6::{
        Fq, Fq6, Fr, G1Affine, G2Affine, FROBENIUS_COEFF_FQ3_C1, FROBENIUS_COEFF_FQ3_C2,
        FROBENIUS_COEFF_FQ6_C1, G1, G2,
    };
    use halo2_proofs::halo2curves::ff::WithSmallOrderMulGroup;
    use halo2_proofs::halo2curves::group::prime::PrimeCurveAffine;
    use halo2_proofs::halo2curves::group::Curve;
    use itertools::Itertools;
    use num_bigint::BigUint;
    use num_traits::Num;

    fn new_pairing_gadget<N: Field>() -> Bw6PairingGadget<N, G1, G2, Halo2Bw6Pairing> {
        let base_field_crt = CrtGadget::new(102, 17, &Fq::modulus());
        let g1: GeneralEccGadget<G1, N> =
            GeneralEccGadget::new(102, &Fr::modulus(), 102, &Fq::modulus(), 17);
        let g2: GeneralEccGadget<G2, N> =
            GeneralEccGadget::new(102, &Fr::modulus(), 102, &Fq::modulus(), 17);

        let zeta = base_field_crt.rns.big_from_uint(&(Fq::ZETA).uint());
        let frobenius_3c1 = base_field_crt
            .rns
            .big_from_uint(&FROBENIUS_COEFF_FQ3_C1[1].uint());
        let frobenius_3c2 = base_field_crt
            .rns
            .big_from_uint(&FROBENIUS_COEFF_FQ3_C2[1].uint());
        let frobenius_6c1 = base_field_crt
            .rns
            .big_from_uint(&FROBENIUS_COEFF_FQ6_C1[1].uint());

        Bw6PairingGadget {
            base_field_crt,
            _g1: g1,
            _g2: g2,
            zeta,
            frobenius_3c1,
            frobenius_3c2,
            frobenius_6c1,
            _marker: std::marker::PhantomData,
        }
    }

    pub(crate) fn pairing_test<N: Field>(
        ac: &mut AbstractCircuit<N>,
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

        let pairing = new_pairing_gadget();

        // {
        //     let p1 = p1
        //         .iter()
        //         .map(|p| pairing.g1.assign_point(ac, &p.to_curve().into()).unwrap())
        //         .collect_vec();

        //     let p2 = p2
        //         .iter()
        //         .map(|p| pairing.g2.assign_point(ac, &p.to_curve().into()).unwrap())
        //         .collect_vec();

        //     pairing.pairing_check(ac, &p1, &p2).unwrap();
        // }

        {
            let p1 = p1
                .iter()
                .map(|p| pairing._g1.assign_point(ac, &p.to_curve().into()).unwrap())
                .collect_vec();

            let (p1_var, p1_fix) = p1.split_at(n_fix);
            let (p2_var, p2_fix) = p2.split_at(n_fix);

            let p2_var = p2_var
                .iter()
                .map(|p| pairing._g2.assign_point(ac, &p.to_curve().into()).unwrap())
                .collect_vec();
            let p2_fix = p2_fix.iter().map(Into::into).collect_vec();
            pairing
                .pairing_check_mixed(ac, p1_var, &p2_var, p1_fix, &p2_fix)
                .unwrap();
        }

        let forced_red = ac.get_log("big-field-forced-red");
        println!("big-field-forced-red: {}", forced_red);
        ac.print_info(false);
    }

    #[test]
    fn test_pairing() {
        use halo2_proofs::halo2curves::bn256::Fr;
        let cfg = AbstractConfig::default();
        let ac = &mut AbstractCircuit::<Fr>::new(cfg);
        let rng = &mut xor_rng();
        pairing_test(ac, rng, 4, 3);
    }

    fn lambda_exp(e: &Fq6) -> Fq6 {
        let r_i = "28d323e134a5dd8d5d387d4ba8f487bf84d6e12a68cc2d52135e42d0ff3f010dd5d8b7279b08997e56ec93f17b1bc533d554658aff2a0f2bf3422352e59f8ab88cbda88b2f316fd54b4eef0b3d16c3969da45c667e271cb976b11ac1be78a3e06a74217d0720132c7499bbefffff7d906bbfffffffff77";
        let r_i = BigUint::from_str_radix(r_i, 16).unwrap();
        e.pow_vartime(r_i.to_u64_digits())
    }

    #[test]
    fn bench_bw6_prover() {
        #[derive(Clone, Default, Copy)]
        struct TestCircuitSynth;
        use halo2_proofs::halo2curves::bn256::Fr;
        impl Synth<Fr> for TestCircuitSynth {
            fn synth(&self, ac: &mut AbstractCircuit<Fr>, _public_inputs: &[Option<Fr>]) {
                let mut rng = xor_rng();
                pairing_test(ac, &mut rng, 4, 3);
            }
        }
        let k = 20;
        let cfg = GateConfig::new(
            6,
            Some(RangeGateConfig::Separate { n: 4 }),
            None,
            None,
            None,
            None,
            None,
            None,
            false,
        );

        run_mock_prover(k, &[], cfg, TestCircuitSynth);
        run_kzg_prover(k, &[], cfg, TestCircuitSynth);
    }

    #[test]
    fn test_residue_gen() {
        use crate::utils::test::xor_rng;
        use halo2_proofs::arithmetic::Field;
        use halo2_proofs::halo2curves::group::Group;
        use halo2_proofs::halo2curves::pairing::MillerLoopResult;
        let mut rng = xor_rng();
        let n = 1;
        let g1 = G1Affine::generator();
        let g2 = G2Affine::generator();
        let scalars = (0..n)
            .map(|_| (Fr::random(&mut rng), Fr::random(&mut rng)))
            .collect::<Vec<_>>();
        let terms = scalars
            .iter()
            .map(|(a, b)| ((g1 * a).to_affine(), (g2 * b).to_affine()))
            .collect::<Vec<_>>();
        let mut terms = terms.iter().map(|(a, b)| (a, b)).collect::<Vec<_>>();

        let last = scalars.iter().fold(Fr::ZERO, |acc, (u0, u1)| acc + u0 * u1);
        let negg1 = -g1;
        let accg2 = (g2 * last).into();
        terms.push((&negg1, &accg2));

        let g1 = terms.iter().map(|(a, _)| *a).cloned().collect::<Vec<_>>();
        let g2 = terms.iter().map(|(_, b)| *b).cloned().collect::<Vec<_>>();
        let u0 = miller_loop(&g1, &g2, &Fq6::one());
        assert_ne!(u0, Fq6::one());
        assert_ne!(u0, Fq6::zero());
        let isone = u0.final_exponentiation();
        assert!(bool::from(isone.is_identity()));
        let c = r_inv(&u0);
        let c = m_inv(&c);

        let w = lambda_exp(&c);
        let w = w * u0.invert().unwrap();
        assert_eq!(w, Fq6::one());
        let u0 = miller_loop(&g1, &g2, &c);
        assert_eq!(u0, Fq6::one());
    }
}
