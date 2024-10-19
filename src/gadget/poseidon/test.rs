use crate::gadget::poseidon::sponge::SpongeGadget;
use crate::Field;
use crate::{gadget::poseidon::reference::Poseidon, ir::ac::AbstractCircuit};
use rand::{Rng, RngCore};

use super::compress::CompressGadget;
use super::reference::{Compress, Sponge};
use super::PoseidonGadget;

#[allow(dead_code)]
pub(crate) fn rand_synth_sponge_gadget<F: Field>(
    ac: &mut AbstractCircuit<F>,
    rng: &mut impl RngCore,
) {
    let r_f = 8;
    let r_p = 55;
    let rate = 2;
    let cap = 1;
    let cfg: Poseidon<F> = Poseidon::generate(r_f, r_p, rate, cap, None);
    let mut sponge_ref = Sponge::new(cfg.clone());
    let cfg = PoseidonGadget::new(cfg);
    let mut sponge = SpongeGadget::new(ac, cfg);

    let test = (0..50)
        .map(|_| {
            (
                (rng.gen_bool(0.5), rng.gen_range(0..=rate * 2 + 1)),
                (rng.gen_bool(0.5), rng.gen_range(0..=rate * 2 + 1)),
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
            sponge.absorb(ac, &inputs);
        });

        do_sq.then(|| {
            let out0 = sponge_ref.squeeze(n_sq);
            let out1 = sponge.squeeze(ac, n_sq);

            out0.iter()
                .zip(out1.iter())
                .for_each(|(&u0, u1)| ac.equal_to_constant(u1, u0).unwrap());
        });
    }
}

#[allow(dead_code)]
pub(crate) fn rand_synth_compress_gadget<F: Field>(
    ac: &mut AbstractCircuit<F>,
    rng: &mut impl RngCore,
) {
    let r_f = 8;
    let r_p = 55;
    let rate = 8;
    let cap = 1;
    let cfg: Poseidon<F> = Poseidon::generate(r_f, r_p, rate, cap, None);

    let input: Vec<F> = (0..rate).map(|_| F::rand(rng)).collect();
    let compress_ref = Compress::new(cfg.clone());
    let u0 = compress_ref.compress(&input);

    let cfg = PoseidonGadget::new(cfg);
    let compress = CompressGadget::new(ac, cfg);
    let input = input
        .iter()
        .map(|e| ac.assign(&e.into()))
        .collect::<Vec<_>>();
    let u1 = compress.compress(ac, &input);
    ac.equal_to_constant(&u1, u0).unwrap();
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
#[cfg(any(feature = "arkworks", feature = "halo2"))]
fn test_compress_gadget() {
    use crate::utils::test::xor_rng;
    #[cfg(feature = "arkworks")]
    use ark_bn254::Fr;
    #[cfg(feature = "halo2")]
    use halo2_proofs::halo2curves::bn256::Fr;
    rand_synth_compress_gadget(&mut AbstractCircuit::<Fr>::default(), &mut xor_rng());
}
