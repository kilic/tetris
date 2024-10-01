use super::{
    ecc_general::GeneralEccGadget,
    ecdsa::EcdsaSignature,
    msm::{multiexp, EccMulGadget},
    Coordinates, Curve, EccGadget,
};
use crate::ir::ac::AbstractConfig;
use crate::{
    gadget::ecc::ecc_base_field::BaseFieldEccGadget, ir::ac::AbstractCircuit, utils::test::xor_rng,
    Field, Value,
};
use rand::RngCore;

#[derive(Debug, Clone, Copy)]
pub(crate) struct MSMSuite {
    n: usize,
    window: usize,
    target: MSMTest,
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum MSMTest {
    VarMSM(VarMSMMethod),
    FixMSM(FixMSMMethod),
}
#[derive(Debug, Clone, Copy)]
pub(crate) enum VarMSMMethod {
    Vertical,
    VerticalMem,
    Horizontal,
    HorizontalMem,
}

impl VarMSMMethod {
    fn iter() -> impl Iterator<Item = Self> {
        vec![
            VarMSMMethod::Vertical,
            VarMSMMethod::VerticalMem,
            VarMSMMethod::Horizontal,
            VarMSMMethod::HorizontalMem,
        ]
        .into_iter()
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum FixMSMMethod {
    ExtendedTable,
    ExtendedTableMem,
    VerticalMem,
    HorizontalMem,
}

impl FixMSMMethod {
    fn iter() -> impl Iterator<Item = Self> {
        vec![
            FixMSMMethod::ExtendedTable,
            FixMSMMethod::ExtendedTableMem,
            FixMSMMethod::VerticalMem,
            FixMSMMethod::HorizontalMem,
        ]
        .into_iter()
    }
}

pub(crate) fn base_field_ecc<C: Curve>(
    sublimb_size: usize,
    limb_size: usize,
) -> BaseFieldEccGadget<C> {
    BaseFieldEccGadget::new(limb_size, &C::Base::modulus(), sublimb_size)
}

pub(crate) fn general_ecc<C: Curve, N: Field>(
    sublimb_size: usize,
    base_limb_size: usize,
    scalar_limb_size: usize,
) -> GeneralEccGadget<C, N> {
    GeneralEccGadget::new(
        scalar_limb_size,
        &C::Scalar::modulus(),
        base_limb_size,
        &C::Base::modulus(),
        sublimb_size,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn msm_test<C: Curve, N: Field>(
    ac: &mut AbstractCircuit<N>,
    ecc: &impl EccMulGadget<C, N>,
    rng: &mut impl RngCore,
    msm: MSMSuite,
) {
    let points: Vec<_> = (0..msm.n).map(|_| C::rand(rng)).collect();
    let scalars: Vec<C::Scalar> = (0..msm.n).map(|_| C::Scalar::rand(rng)).collect();
    let res0 = multiexp(&points[..], &scalars[..]);

    let scalars = scalars
        .into_iter()
        .map(|e| ecc.assign_scalar(ac, &e.into()))
        .collect::<Vec<_>>();

    let res1 = match msm.target {
        MSMTest::VarMSM(method) => {
            let points = points
                .into_iter()
                .map(|e| ecc.assign_point(ac, &e.into()))
                .collect::<Result<Vec<_>, _>>()
                .unwrap();

            match method {
                VarMSMMethod::Vertical => ecc.msm_var_vertical(ac, msm.window, &points, &scalars),
                VarMSMMethod::VerticalMem => {
                    ecc.msm_var_vertical_with_mem(ac, msm.window, &points, &scalars)
                }
                VarMSMMethod::Horizontal => {
                    ecc.msm_var_horizontal(ac, msm.window, &points, &scalars)
                }
                VarMSMMethod::HorizontalMem => {
                    ecc.msm_var_horizontal_with_mem(ac, msm.window, &points, &scalars)
                }
            }
        }
        MSMTest::FixMSM(method) => match method {
            FixMSMMethod::ExtendedTable => {
                ecc.msm_fix_vertical_extended(ac, msm.window, &points, &scalars)
            }
            FixMSMMethod::ExtendedTableMem => {
                ecc.msm_fix_vertical_extended(ac, msm.window, &points, &scalars)
            }
            FixMSMMethod::VerticalMem => {
                ecc.msm_fix_vertical_mem(ac, msm.window, &points, &scalars)
            }
            FixMSMMethod::HorizontalMem => {
                ecc.msm_fix_horizontal_mem(ac, msm.window, &points, &scalars)
            }
        },
    };

    res1.value().map(|res1| assert_eq!(res0, res1));
    let res0 = ecc.assign_point(ac, &res0.into()).unwrap();
    ecc.normal_equal(ac, &res0, &res1).unwrap();
}

fn run_msm_test<C: Curve, N: Field>(ecc: &impl EccMulGadget<C, N>) {
    let n_limbs = ecc.base_field_crt().rns().n_limbs();
    let rng = &mut xor_rng();

    let cfg = AbstractConfig::new(
        n_limbs.into(),
        n_limbs.into(),
        Default::default(),
        Default::default(),
        Default::default(),
        Default::default(),
        true,
    );

    for target in VarMSMMethod::iter() {
        let mut ac = AbstractCircuit::<N>::new(cfg.clone());
        let msm = MSMSuite {
            n: 1,
            window: 4,
            target: MSMTest::VarMSM(target),
        };
        msm_test::<C, N>(&mut ac, ecc, rng, msm);
    }

    for target in VarMSMMethod::iter() {
        let mut ac = AbstractCircuit::<N>::new(cfg.clone());
        let msm = MSMSuite {
            n: 2,
            window: 4,
            target: MSMTest::VarMSM(target),
        };
        msm_test::<C, N>(&mut ac, ecc, rng, msm);
    }

    for target in VarMSMMethod::iter() {
        let mut ac = AbstractCircuit::<N>::new(cfg.clone());
        let msm = MSMSuite {
            n: 50,
            window: 6,
            target: MSMTest::VarMSM(target),
        };
        msm_test::<C, N>(&mut ac, ecc, rng, msm);
    }

    for target in FixMSMMethod::iter() {
        let mut ac = AbstractCircuit::<N>::new(cfg.clone());
        let msm = MSMSuite {
            n: 1,
            window: 4,
            target: MSMTest::FixMSM(target),
        };
        msm_test::<C, N>(&mut ac, ecc, rng, msm);
    }

    for target in FixMSMMethod::iter() {
        let mut ac = AbstractCircuit::<N>::new(cfg.clone());
        let msm = MSMSuite {
            n: 2,
            window: 4,
            target: MSMTest::FixMSM(target),
        };
        msm_test::<C, N>(&mut ac, ecc, rng, msm);
    }

    for target in FixMSMMethod::iter() {
        let mut ac = AbstractCircuit::<N>::new(cfg.clone());
        let msm = MSMSuite {
            n: 50,
            window: 6,
            target: MSMTest::FixMSM(target),
        };
        msm_test::<C, N>(&mut ac, ecc, rng, msm);
    }
}

#[test]
#[cfg(any(feature = "arkworks", feature = "halo2"))]
fn test_msm() {
    #[cfg(feature = "arkworks")]
    use ark_bn254::G1Projective as G1;
    #[cfg(feature = "halo2")]
    use halo2_proofs::halo2curves::bn256::G1;
    run_msm_test(&base_field_ecc::<G1>(15, 90));
}

pub(crate) fn ecc_operations_test<C: Curve, N: Field>(
    ac: &mut AbstractCircuit<N>,
    ecc: &impl EccMulGadget<C, N>,
    rng: &mut impl RngCore,
) {
    // constant registry
    {
        let p = C::rand(rng);
        let p_val = p.into();
        let p_assigned = ecc.assign_point(ac, &p_val).unwrap();
        let p_constant = ecc.get_constant(ac, &p);
        ecc.assert_on_curve(ac, &p_constant).unwrap();
        ecc.copy_equal(ac, &p_assigned, &p_constant).unwrap();
        ecc.normal_equal(ac, &p_assigned, &p_constant).unwrap();
    }

    // add
    {
        let a: Value<C> = C::rand(rng).into();
        let b: Value<C> = C::rand(rng).into();
        let c: Value<C> = a + b;
        let a = ecc.assign_point(ac, &a).unwrap();
        let b = ecc.assign_point(ac, &b).unwrap();
        let c0 = ecc.assign_point(ac, &c).unwrap();
        let c1 = ecc.add_incomplete(ac, &a, &b);
        ecc.normal_equal(ac, &c0, &c1).unwrap();

        let a: Value<C> = C::rand(rng).into();
        let b: Value<C> = C::rand(rng).into();
        let c: Value<C> = a - b;
        let a = ecc.assign_point(ac, &a).unwrap();
        let b = ecc.assign_point(ac, &b).unwrap();
        let c0 = ecc.assign_point(ac, &c).unwrap();
        let c1 = ecc.sub_incomplete(ac, &a, &b);
        ecc.normal_equal(ac, &c0, &c1).unwrap();

        let n = 50;
        let points: Vec<C> = (0..n).map(|_| C::rand(rng)).collect();
        let sum = points.iter().fold(C::identity(), |acc, p| acc + *p);
        let u0 = ecc.assign_point(ac, &sum.into()).unwrap();
        let points = points
            .into_iter()
            .map(|p| ecc.assign_point(ac, &p.into()).unwrap())
            .collect::<Vec<_>>();
        let u1 = ecc.add_chain(ac, &points[..]);
        ecc.normal_equal(ac, &u0, &u1).unwrap();
    }

    // double
    {
        let a: Value<C> = C::rand(rng).into();
        let c = a + a;
        let a = ecc.assign_point(ac, &a).unwrap();
        let c0 = ecc.assign_point(ac, &c).unwrap();
        let c1 = ecc.double_incomplete(ac, &a);
        ecc.normal_equal(ac, &c0, &c1).unwrap();
    }
}

fn run_ecc_operations_test<C: Curve, N: Field>(ecc: &impl EccMulGadget<C, N>) {
    let n_limbs = ecc.base_field_crt().rns().n_limbs();
    let cfg = AbstractConfig::new(
        n_limbs.into(),
        n_limbs.into(),
        Default::default(),
        Default::default(),
        Default::default(),
        Default::default(),
        true,
    );
    let rng = &mut xor_rng();
    let mut ac = AbstractCircuit::<N>::new(cfg);
    ecc_operations_test::<C, N>(&mut ac, ecc, rng);
}

#[test]
#[cfg(any(feature = "arkworks", feature = "halo2"))]
fn test_ecc_operations() {
    #[cfg(feature = "arkworks")]
    use ark_bn254::{Fr, G1Projective as G1};
    #[cfg(feature = "arkworks")]
    use ark_secp256k1::Projective as Secp256k1;
    #[cfg(feature = "halo2")]
    use halo2_proofs::halo2curves::{
        bn256::{Fr, G1},
        secp256k1::Secp256k1,
    };

    run_ecc_operations_test(&base_field_ecc::<G1>(15, 90));
    run_ecc_operations_test(&general_ecc::<Secp256k1, Fr>(15, 90, 90));
}

pub(crate) fn ecdsa_test<C: Curve, N: Field>(
    ac: &mut AbstractCircuit<N>,
    ecc: &GeneralEccGadget<C, N>,
    rng: &mut impl RngCore,
) {
    // Generate a key pair
    let g = C::generator(); // Generate a key pair
    let private_key = C::Scalar::rand(rng);
    let public_key = g * private_key;

    // Generate a valid signature
    let message = C::Scalar::rand(rng);

    // Draw arandomness
    let k = C::Scalar::rand(rng);
    let k_inv = k.inv().unwrap();

    // Calculate `r`
    let r_point = (g * k).coords();
    let x = r_point.x();
    let r: C::Scalar = x.cast();

    // Calculate `s`
    let s = k_inv * (message + (r * private_key));

    // Make sure we construct a valid ECDSA signature
    {
        let s_inv = s.inv().unwrap();
        let u_1 = message * s_inv;
        let u_2 = r * s_inv;
        let r_point = ((g * u_1) + (public_key * u_2)).coords();
        let x_candidate = r_point.x();
        let r_candidate = x_candidate.cast();
        assert_eq!(r, r_candidate);
    }

    let public_key = ecc.assign_point(ac, &public_key.into()).unwrap();
    let message = ecc.assign_scalar(ac, &message.into());
    let r = ecc.assign_scalar(ac, &r.into());
    let s = ecc.assign_scalar(ac, &s.into());
    let signature = EcdsaSignature { r, s };

    ecc.ecdsa_assert_verify(ac, g, &public_key, &message, &signature)
        .unwrap();
}

fn run_ecdsa_test<C: Curve, N: Field>(ecc: &GeneralEccGadget<C, N>) {
    let n_limbs = ecc.base_field_crt().rns().n_limbs();
    let cfg = AbstractConfig::new(
        n_limbs.into(),
        n_limbs.into(),
        Default::default(),
        Default::default(),
        Default::default(),
        Default::default(),
        true,
    );
    let rng = &mut xor_rng();
    let mut ac = AbstractCircuit::<N>::new(cfg);
    ecdsa_test::<C, N>(&mut ac, ecc, rng);
}

#[test]
fn test_ecdsa() {
    #[cfg(feature = "arkworks")]
    use ark_bn254::Fr;
    #[cfg(feature = "arkworks")]
    use ark_secp256k1::Projective as Secp256k1;
    #[cfg(feature = "halo2")]
    use halo2_proofs::halo2curves::{bn256::Fr, secp256k1::Secp256k1};
    run_ecdsa_test(&general_ecc::<Secp256k1, Fr>(15, 90, 90));
}
