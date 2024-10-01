use crate::gadget::ecc::msm::{multiexp, EccMulGadget};
use crate::gadget::ecc::test::base_field_ecc;
use crate::gadget::ecc::Curve;
use crate::gadget::poseidon::test::rand_synth_sponge_gadget;
use crate::gadget::rsa::test::rsa_test;
use crate::halo2::config::{
    GateConfig, Gates, StaticLayoutConfig, TernaryLookupConfig, VectorLookupConfig,
};
use crate::Field;
use crate::{
    gadget::big_field::test::crt_garget_test,
    halo2::config::RangeGateConfig,
    ir::test::{
        rand_synth_arithmetic_ir, rand_synth_linear_combination_ir, rand_synth_memro_ir,
        rand_synth_memwo_ir, rand_synth_public_inputs_ir, rand_synth_quad_composions_ir,
        rand_synth_range_combinations_ir, rand_synth_select_ir,
    },
    utils::test::xor_rng,
    Value,
};
use crate::{
    halo2::LayoutCtx,
    ir::ac::{AbstractCircuit, AbstractConfig},
};
use ark_std::{end_timer, start_timer};
use halo2_proofs::halo2curves::bn256::G1;
use halo2_proofs::plonk::verify_proof_multi;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    halo2curves::{bn256::Fr, ff::PrimeField},
    plonk::{Circuit, ConstraintSystem, ErrorFront},
};
use halo2_proofs::{
    dev::MockProver,
    halo2curves::{bn256::Bn256, ff::FromUniformBytes},
    plonk::{create_proof, keygen_pk, keygen_vk},
    poly::{
        commitment::ParamsProver,
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverSHPLONK, VerifierSHPLONK},
            strategy::AccumulatorStrategy,
        },
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};
use num_bigint::BigUint;
use num_traits::Num;
use rand_core::OsRng;
use rsa::RsaPrivateKey;

pub(crate) trait Synth<F: PrimeField + Ord>: Clone + Default {
    fn synth(&self, ac: &mut AbstractCircuit<F>, public_inputs: &[Option<F>]);
}

#[derive(Clone, Default)]
struct TestCircuit<F: PrimeField + Ord, S: Synth<F>> {
    cfg: GateConfig,
    public_inputs: Vec<Option<F>>,
    synth: S,
}

impl<F: PrimeField + Ord, S: Synth<F>> TestCircuit<F, S> {
    fn abstract_cfg(&self) -> AbstractConfig {
        self.cfg.abstract_cfg()
    }

    fn cfg(&self, meta: &mut ConstraintSystem<F>) -> Gates {
        Gates::configure(meta, &self.cfg)
    }
}

impl<F: PrimeField + Ord, S: Synth<F>> Circuit<F> for TestCircuit<F, S> {
    type Config = Gates;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = Self;

    fn configure_with_params(meta: &mut ConstraintSystem<F>, params: Self::Params) -> Self::Config {
        params.cfg(meta)
    }

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(_: &mut ConstraintSystem<F>) -> Self::Config {
        unreachable!()
    }

    fn synthesize(&self, cfg: Self::Config, ly: impl Layouter<F>) -> Result<(), ErrorFront> {
        let mut ac = AbstractCircuit::new(self.abstract_cfg());
        self.synth.synth(&mut ac, &self.public_inputs);
        cfg.layout(&mut LayoutCtx::new(ly), &ac)
    }

    fn params(&self) -> Self::Params {
        self.clone()
    }
}

pub(crate) fn run_mock_prover<F: Ord + FromUniformBytes<64>>(
    k: u32,
    public_inputs: &[F],
    cfg: GateConfig,
    synth: impl Synth<F>,
) {
    let circuit = TestCircuit {
        cfg,
        public_inputs: public_inputs.iter().map(|pi| Some(*pi)).collect(),
        synth,
    };

    let prover = match MockProver::run(k, &circuit, vec![public_inputs.to_vec()]) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#?}"),
    };
    prover.assert_satisfied();
}

#[allow(dead_code)]
pub(crate) fn run_kzg_prover(k: u32, public_inputs: &[Fr], cfg: GateConfig, synth: impl Synth<Fr>) {
    let circuit = TestCircuit {
        cfg,
        public_inputs: public_inputs.iter().map(|pi| Some(*pi)).collect(),
        synth,
    };

    let params = ParamsKZG::<Bn256>::new(k);
    let vk = keygen_vk(&params, &circuit).unwrap();
    let pk = keygen_pk(&params, vk.clone(), &circuit).unwrap();

    let t_prover = start_timer!(|| "prover");
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<Bn256>, _, _, _, _>(
        &params,
        &pk,
        &[circuit],
        &[vec![public_inputs.to_vec()]],
        OsRng,
        &mut transcript,
    )
    .unwrap();
    let proof = transcript.finalize();
    end_timer!(t_prover);

    let params = params.verifier_params();
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    let verified = verify_proof_multi::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<_>,
        _,
        _,
        AccumulatorStrategy<Bn256>,
    >(
        &params,
        &vk,
        &[vec![public_inputs.to_vec()]],
        &mut transcript,
    );

    assert!(verified);
}

#[test]
fn test_halo2_acc_gate() {
    #[derive(Clone, Default, Copy)]
    struct TestCircuitSynth;

    impl<F: PrimeField + Ord> Synth<F> for TestCircuitSynth {
        fn synth(&self, ac: &mut AbstractCircuit<F>, public_inputs: &[Option<F>]) {
            let mut rng = xor_rng();
            let pi: Vec<Value<F>> = public_inputs
                .iter()
                .map(|e| (*e).into())
                .collect::<Vec<_>>();
            rand_synth_public_inputs_ir(ac, &pi);
            rand_synth_arithmetic_ir(ac, &mut rng);
            rand_synth_linear_combination_ir(ac, true, &mut rng);
            rand_synth_quad_composions_ir(ac, true, &mut rng);
            rand_synth_range_combinations_ir(ac, &mut rng);
            rand_synth_select_ir(ac, &mut rng);
        }
    }

    let k = 17;
    let public_inputs = [12, 13, 14]
        .iter()
        .map(|x| Fr::from(*x))
        .collect::<Vec<_>>();

    let cfg = GateConfig::new(
        2,
        Some(RangeGateConfig::Shared),
        None,
        None,
        None,
        None,
        None,
        None,
        true,
    );
    run_mock_prover::<Fr>(k, &public_inputs, cfg, TestCircuitSynth);
    // run_kzg_prover(k, &public_inputs, cfg, TestCircuitSynth);

    let cfg = GateConfig::new(
        2,
        Some(RangeGateConfig::Separate { n: 2 }),
        None,
        None,
        None,
        None,
        None,
        None,
        true,
    );
    run_mock_prover::<Fr>(k, &public_inputs, cfg, TestCircuitSynth);
    // run_kzg_prover(k, &[], cfg, TestCircuitSynth);

    let cfg = GateConfig::new(
        2,
        Some(RangeGateConfig::Separate { n: 2 }),
        None,
        None,
        Some(StaticLayoutConfig { offset: 0 }),
        None,
        None,
        None,
        true,
    );
    run_mock_prover::<Fr>(k, &public_inputs, cfg, TestCircuitSynth);
    // run_kzg_prover(k, &[], cfg, TestCircuitSynth);
}

#[test]
fn test_halo2_range_gate() {
    #[derive(Clone, Default, Copy)]
    struct TestCircuitSynth;

    impl<F: PrimeField + Ord> Synth<F> for TestCircuitSynth {
        fn synth(&self, ac: &mut AbstractCircuit<F>, _public_inputs: &[Option<F>]) {
            let mut rng = xor_rng();
            rand_synth_range_combinations_ir(ac, &mut rng);
        }
    }
    let k = 16;
    let cfg = GateConfig::new(
        2,
        Some(RangeGateConfig::Shared),
        None,
        None,
        None,
        None,
        None,
        None,
        true,
    );
    run_mock_prover::<Fr>(k, &[], cfg, TestCircuitSynth);
    // run_kzg_prover(k, &[], cfg, TestCircuitSynth);
}

#[test]
fn test_halo2_memwo_gate() {
    #[derive(Clone, Default, Copy)]
    struct TestCircuitSynth;

    impl<F: PrimeField + Ord> Synth<F> for TestCircuitSynth {
        fn synth(&self, ac: &mut AbstractCircuit<F>, _public_inputs: &[Option<F>]) {
            let mut rng = xor_rng();
            rand_synth_memwo_ir(ac, &mut rng).unwrap();
        }
    }

    let k = 12;
    let cfg = GateConfig::new(
        2,
        None,
        None,
        Some(VectorLookupConfig {
            offset: 0,
            width: 4,
        }),
        None,
        None,
        None,
        None,
        true,
    );
    run_mock_prover::<Fr>(k, &[], cfg, TestCircuitSynth);
    // run_kzg_prover(k, &[], cfg, TestCircuitSynth);
}

#[test]
fn test_halo2_memro_gate() {
    #[derive(Clone, Default, Copy)]
    struct TestCircuitSynth;

    impl<F: PrimeField + Ord> Synth<F> for TestCircuitSynth {
        fn synth(&self, ac: &mut AbstractCircuit<F>, _public_inputs: &[Option<F>]) {
            let mut rng = xor_rng();
            rand_synth_memro_ir(ac, &mut rng).unwrap();
        }
    }

    let k = 12;
    let cfg = GateConfig::new(
        2,
        None,
        Some(VectorLookupConfig {
            offset: 0,
            width: 4,
        }),
        None,
        None,
        None,
        None,
        None,
        true,
    );
    run_mock_prover::<Fr>(k, &[], cfg, TestCircuitSynth);
    // run_kzg_prover(k, &[], cfg, TestCircuitSynth);
}

#[test]
fn test_halo2_crt() {
    #[derive(Clone, Default)]
    struct TestCircuitSynth {
        limb_size: usize,
        sublimb_size: usize,
        modulus: BigUint,
    }
    impl<F: PrimeField + Ord> Synth<F> for TestCircuitSynth {
        fn synth(&self, ac: &mut AbstractCircuit<F>, _public_inputs: &[Option<F>]) {
            let mut rng = xor_rng();
            crt_garget_test(
                ac,
                &mut rng,
                &self.modulus,
                self.limb_size,
                self.sublimb_size,
            );
        }
    }

    fn run(limb_size: usize, sublimb_size: usize, modulus: &str) {
        let k = 18;
        let cfg = GateConfig::new(
            4,
            Some(RangeGateConfig::Shared),
            None,
            None,
            None,
            None,
            None,
            None,
            true,
        );

        let circuit = TestCircuitSynth {
            limb_size,
            sublimb_size,
            modulus: BigUint::from_str_radix(modulus, 10).unwrap(),
        };
        run_mock_prover::<Fr>(k, &[], cfg, circuit.clone());
        // run_kzg_prover(k, &[], cfg, circuit);
    }

    // BN base field modulus
    run(
        90,
        15,
        "21888242871839275222246405745257275088696311157297823662689037894645226208583",
    );
    // BLS base field modulus
    run(90,15,"4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787");
    // BW6 base field modulus
    run(90,15,"6891450384315732539396789682275657542479668912536150109513790160209623422243491736087683183289411687640864567753786613451161759120554247759349511699125301598951605099378508850372543631423596795951899700429969112842764913119068299");
    // 2048 RSA modulus
    run(90,15,"25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357");
}

#[test]
fn test_halo2_poseidon() {
    #[derive(Clone, Default, Copy)]
    struct TestCircuitSynth;
    impl<F: PrimeField + Ord> Synth<F> for TestCircuitSynth {
        fn synth(&self, ac: &mut AbstractCircuit<F>, _public_inputs: &[Option<F>]) {
            let mut rng = xor_rng();
            rand_synth_sponge_gadget(ac, &mut rng);
        }
    }
    let k = 18;
    let cfg = GateConfig::new(4, None, None, None, None, None, None, None, true);
    run_mock_prover::<Fr>(k, &[], cfg, TestCircuitSynth);
}

#[test]
fn test_halo2_rsa() {
    #[derive(Clone, Default)]
    struct TestCircuitSynth {
        limb_size: usize,
        sublimb_size: usize,
        msg_len: usize,
        priv_key: Option<RsaPrivateKey>,
    }

    impl<F: PrimeField + Ord> Synth<F> for TestCircuitSynth {
        fn synth(&self, ac: &mut AbstractCircuit<F>, _public_inputs: &[Option<F>]) {
            let mut rng = xor_rng();
            rsa_test(
                ac,
                &mut rng,
                self.priv_key.clone(),
                self.msg_len,
                self.limb_size,
                self.sublimb_size,
            );
        }
    }
    let k = 17;
    let cfg = GateConfig::new(
        3,
        Some(RangeGateConfig::Shared),
        None,
        None,
        None,
        None,
        Some(TernaryLookupConfig {
            offset: 0,
            size_hint: 8,
        }),
        Some(TernaryLookupConfig {
            offset: 0,
            size_hint: 8,
        }),
        true,
    );
    let priv_key = RsaPrivateKey::new(&mut OsRng, 2048).unwrap();
    let circuit = TestCircuitSynth {
        limb_size: 90,
        sublimb_size: 15,
        msg_len: 1000,
        priv_key: Some(priv_key),
    };
    run_mock_prover::<Fr>(k, &[], cfg, circuit.clone());
    // run_kzg_prover(k, &[], cfg, circuit);
}

#[test]
fn test_halo2_ecc() {
    fn run_msm<C: Curve, N: Field>(
        ac: &mut AbstractCircuit<N>,
        ecc: &impl EccMulGadget<C, N>,
        n_points: usize,
        window: usize,
    ) {
        let rng = &mut xor_rng();
        let points: Vec<_> = (0..n_points).map(|_| C::rand(rng)).collect();
        let scalars: Vec<C::Scalar> = (0..n_points).map(|_| C::Scalar::rand(rng)).collect();
        let res0 = multiexp(&points[..], &scalars[..]);
        let t = start_timer!(|| "abstract circuit witgen");
        let scalars = scalars
            .into_iter()
            .map(|e| ecc.assign_scalar(ac, &e.into()))
            .collect::<Vec<_>>();
        let points = points
            .into_iter()
            .map(|e| ecc.assign_point(ac, &e.into()))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let res1 = ecc.msm_var_horizontal_with_mem(ac, window, &points, &scalars);
        res1.value().map(|res1| assert_eq!(res0, res1));
        let res0 = ecc.assign_point(ac, &res0.into()).unwrap();
        ecc.normal_equal(ac, &res0, &res1).unwrap();
        end_timer!(t);
        ac.print_info(false);
    }

    #[derive(Clone, Default)]
    struct TestCircuitSynth;

    impl Synth<Fr> for TestCircuitSynth {
        fn synth(&self, ac: &mut AbstractCircuit<Fr>, _public_inputs: &[Option<Fr>]) {
            let ecc = &base_field_ecc::<G1>(15, 90);
            run_msm(ac, ecc, 100, 6);
        }
    }
    let k = 18;
    let cfg = GateConfig::new(
        4,
        Some(RangeGateConfig::Separate { n: 4 }),
        None,
        Some(VectorLookupConfig {
            offset: 0,
            width: 3, // number of limbs
        }),
        None,
        None,
        None,
        None,
        false,
    );
    run_mock_prover::<Fr>(k, &[], cfg, TestCircuitSynth);
    // run_kzg_prover(k, &[], cfg, TestCircuitSynth);
}

// #[test]
// fn test_halo2_pairing() {
//     #[derive(Clone, Default, Copy)]
//     struct TestCircuitSynth;
//     impl Synth<Fr> for TestCircuitSynth {
//         fn synth(&self, ac: &mut AbstractCircuit<Fr>, _public_inputs: &[Option<Fr>]) {
//             let mut rng = xor_rng();
//             use crate::gadget::ecc::bn_pairing::halo2::test::pairing_test;
//             pairing_test(ac, &mut rng, 4, 3);
//         }
//     }
//     let k = 21;
//     let cfg = GateConfig::new(
//         4,
//         Some(RangeGateConfig::Shared),
//         None,
//         None,
//         None,
//         None,
//         None,
//         None,
//         true,
//     );
//     run_mock_prover::<Fr>(k, &[], cfg, TestCircuitSynth);
//     // run_kzg_prover(k, &[], cfg, TestCircuitSynth);
// }
