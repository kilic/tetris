use crate::Field;
use crate::{
    gadget::poseidon::{
        reference::{Poseidon, PoseidonSponge},
        PoseidonSpongeGadget,
    },
    ir::ac::AbstractCircuit,
};
use rand::{Rng, RngCore};

#[allow(dead_code)]
pub(crate) fn rand_synth_sponge_gadget<F: Field>(
    ac: &mut AbstractCircuit<F>,
    rng: &mut impl RngCore,
) {
    let cfg: Poseidon<F> = Poseidon::generate(8, 55, 2, 1, None);
    let mut sponge_ref = PoseidonSponge::new(&cfg);
    let mut sponge = PoseidonSpongeGadget::new(ac, &cfg);

    let test = (0..50)
        .map(|_| {
            (
                (rng.gen_bool(0.5), rng.gen_range(0..=cfg.rate * 2 + 1)),
                (rng.gen_bool(0.5), rng.gen_range(0..=cfg.rate * 2 + 1)),
            )
        })
        .collect::<Vec<_>>();

    for test in test.iter() {
        let (do_ab, n_ab) = test.0;
        let (do_sq, n_sq) = test.1;

        do_ab.then(|| {
            let inputs = (0..n_ab).map(|_| F::rand(rng)).collect::<Vec<_>>();
            sponge_ref.absorb(&inputs);
            let inputs = inputs
                .iter()
                .map(|e| ac.var(&(*e).into()))
                .collect::<Vec<_>>();
            sponge.absorb(&inputs);
        });

        do_sq.then(|| {
            let out0 = sponge_ref.squeeze(n_sq);
            let out1 = sponge.squeeze(ac, n_sq);

            out0.iter().zip(out1.iter()).for_each(|(u0, u1)| {
                let u0 = ac.assign(&(*u0).into());
                ac.equal(u0.as_ref(), u1).unwrap()
            });
        });
    }
}

#[test]
#[cfg(any(feature = "arkworks", feature = "halo2"))]
fn test_sponge_gadget() {
    use crate::utils::test::xor_rng;
    #[cfg(feature = "arkworks")]
    use ark_bn254::Fr;
    #[cfg(feature = "halo2")]
    use halo2_proofs::halo2curves::bn256::Fr;
    rand_synth_sponge_gadget(&mut AbstractCircuit::<Fr>::default(), &mut xor_rng());
}

#[test]
#[cfg(feature = "arkworks")]
fn test_parameters_cross() {
    use ark_bn254::Fr;
    use ark_crypto_primitives::sponge::poseidon::find_poseidon_ark_and_mds;
    use ark_ff::PrimeField;

    let rate = 2;
    let r_f = 8;
    let r_p = 55;

    let (constants, mds) =
        find_poseidon_ark_and_mds::<Fr>(Fr::MODULUS_BIT_SIZE as u64, rate, r_f, r_p, 0);
    let local = Poseidon::<Fr>::generate(r_f as usize, r_p as usize, rate, 1, None);
    assert_eq!(local.constants, constants);
    assert_eq!(
        local.mds.els,
        mds.iter().flatten().cloned().collect::<Vec<Fr>>()
    );
}

#[allow(dead_code)]
fn poseidon_test_vectors<F: Field>() {
    use num_bigint::BigUint;
    use num_traits::Num;

    // https://extgit.iaik.tugraz.at/krypto/hadeshash/-/blob/master/code/test_vectors.txt
    // poseidonperm_x5_254_3
    {
        const R_F: usize = 8;
        const R_P: usize = 57;
        const RATE: usize = 2;

        let mut state = vec![0u64, 1, 2]
            .into_iter()
            .map(F::from_u64)
            .collect::<Vec<F>>();
        let poseidon: Poseidon<F> = Poseidon::generate(R_F, R_P, RATE, 1, None);

        poseidon.permute(&mut state);

        let expected = [
            "7853200120776062878684798364095072458815029376092732009249414926327459813530",
            "7142104613055408817911962100316808866448378443474503659992478482890339429929",
            "6549537674122432311777789598043107870002137484850126429160507761192163713804",
        ];
        let expected = expected
            .iter()
            .map(|e| BigUint::from_str_radix(e, 10).unwrap());
        state
            .into_iter()
            .zip(expected)
            .for_each(|(word, expected)| assert_eq!(word.uint(), expected));
    }

    // https://extgit.iaik.tugraz.at/krypto/hadeshash/-/blob/master/code/test_vectors.txt
    // poseidonperm_x5_254_5
    {
        const R_F: usize = 8;
        const R_P: usize = 60;
        const RATE: usize = 4;

        let mut state = vec![0u64, 1, 2, 3, 4]
            .into_iter()
            .map(F::from_u64)
            .collect::<Vec<F>>();
        let poseidon: Poseidon<F> = Poseidon::generate(R_F, R_P, RATE, 1, None);

        poseidon.permute(&mut state);

        let expected = [
            "18821383157269793795438455681495246036402687001665670618754263018637548127333",
            "7817711165059374331357136443537800893307845083525445872661165200086166013245",
            "16733335996448830230979566039396561240864200624113062088822991822580465420551",
            "6644334865470350789317807668685953492649391266180911382577082600917830417726",
            "3372108894677221197912083238087960099443657816445944159266857514496320565191",
        ];
        let expected = expected
            .iter()
            .map(|e| BigUint::from_str_radix(e, 10).unwrap());
        state
            .into_iter()
            .zip(expected)
            .for_each(|(word, expected)| assert_eq!(word.uint(), expected));
    }
}

#[cfg(any(feature = "arkworks", feature = "halo2"))]
#[test]
fn test_poseidon_test_vectors() {
    #[cfg(feature = "arkworks")]
    use ark_bn254::Fr;
    #[cfg(feature = "halo2")]
    use halo2_proofs::halo2curves::bn256::Fr;
    poseidon_test_vectors::<Fr>();
}
