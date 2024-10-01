use super::{
    ac::{AbstractCircuit, AbstractConfig},
    combination::{linear::Lc, quad::Qc, CombinationGadget},
};
use crate::{
    ir::{
        bitwise::BitwiseIRConfig, combination::CombinationIR, mem::MemIRConfig, pow5::Pow5IRConfig,
        select::SelectIRConfig,
    },
    utils::log2,
};
use crate::{lc, qc, Error, Field, QuadScaled, Scaled, Term, Value, Var};
use itertools::Itertools;
use num_integer::div_ceil;
use rand::Rng;
use rand::RngCore;

impl<F: Field> AbstractCircuit<F> {
    pub fn rand_var(&mut self, rng: &mut impl RngCore) -> Var<F> {
        self.var(&F::rand(rng).into())
    }

    pub fn rand_var_assigned(&mut self, rng: &mut impl RngCore) -> Var<F> {
        self.assign(&F::rand(rng).into())
    }

    pub fn rand_var_in_range(&mut self, size: usize, rng: &mut impl RngCore) -> Var<F> {
        self.var(&F::rand_in_range(rng, false, size).into())
    }

    pub fn rand_signed_var_in_range(&mut self, size: usize, rng: &mut impl RngCore) -> Var<F> {
        self.var(&F::rand_in_range(rng, true, size).into())
    }

    pub fn rand_scaled(&mut self, rng: &mut impl RngCore) -> Scaled<F> {
        self.rand_var(rng) * F::rand(rng)
    }

    pub fn rand_quad_scaled(&mut self, rng: &mut impl RngCore) -> QuadScaled<F> {
        self.rand_var(rng) * self.rand_var(rng) * F::rand(rng)
    }
}

pub fn rand_synth_public_inputs_ir<F: Field>(ac: &mut AbstractCircuit<F>, pi: &[Value<F>]) {
    let pi0 = pi
        .iter()
        .map(|v| {
            let w = ac.var(v);
            ac.public(&w);
            w
        })
        .collect::<Vec<_>>();
    let pi1 = pi.iter().map(|v| ac.assign(v)).collect::<Vec<_>>();
    pi0.iter().zip(pi1.iter()).for_each(|(p0, p1)| {
        ac.equal(p0, p1).unwrap();
    });
}

pub fn rand_synth_linear_combination_ir<F: Field>(
    ac: &mut AbstractCircuit<F>,
    use_constants: bool,
    rng: &mut impl RngCore,
) {
    let w0 = &ac.rand_var_assigned(rng);
    ac.equal(w0, w0).unwrap();
    let constant: F = if use_constants {
        F::rand(rng)
    } else {
        F::zero()
    };

    for n_terms in 1..20 {
        let mut lc0 = lc!(constant);
        lc0 += (0..n_terms).map(|_| ac.rand_scaled(rng));

        let v0 = lc0.value();
        let mut lc1 = lc0.clone();
        let u0 = ac.eval(lc0);

        let u1 = ac.assign(&v0);

        u0.value()
            .zip(u1.value())
            .map(|(e0, e1)| assert_eq!(e0, e1));

        ac.equal(&u0, &u1).unwrap();

        lc1 -= u1;
        ac.zero_sum(lc1).unwrap();
    }
}

pub fn rand_synth_range_combinations_ir<F: Field>(
    ac: &mut AbstractCircuit<F>,
    rng: &mut impl RngCore,
) {
    for limb_size in 1..=8 {
        for size in 1..limb_size * 5 + 1 {
            let n_limbs = div_ceil(size, limb_size);
            for _ in 0..11 {
                let var0 = ac.rand_var_in_range(size, rng);
                let limbs = ac.decompose(limb_size, size, &var0).unwrap();
                assert!(limbs.len() == n_limbs);
                let var1 = ac.compose(&limbs, limb_size);
                ac.equal(&var0, &var1).unwrap();
            }
        }
    }

    for limb_size in 1..=8 {
        for size in 1..limb_size * 5 + 1 {
            for _ in 0..11 {
                let n_limbs = div_ceil(size, limb_size);
                let var0 = ac.rand_signed_var_in_range(size, rng);
                let limbs = ac.decompose_signed(limb_size, size, &var0).unwrap();
                assert!(limbs.len() == n_limbs);
                let var1 = ac.compose(&limbs, limb_size);
                ac.equal(&var0, &var1).unwrap();
            }
        }
    }

    for _ in 0..10 {
        for n_limbs in 1..10 {
            let sizes = (0..n_limbs).map(|_| rng.gen_range(1..10)).collect_vec();
            let size = sizes.iter().sum::<usize>();
            let var0 = ac.rand_var_in_range(size, rng);
            let limbs = ac.decompose_nonuniform(&sizes, &var0).unwrap();
            assert!(limbs.len() == n_limbs);
            let var1 = ac.compose_nonuniform(&limbs, &sizes);
            ac.equal(&var0, &var1).unwrap();
        }
    }
}

pub fn rand_synth_quad_composions_ir<F: Field>(
    ac: &mut AbstractCircuit<F>,
    use_constants: bool,
    rng: &mut impl RngCore,
) {
    let constant: F = if use_constants {
        F::rand(rng)
    } else {
        F::zero()
    };

    for n_lin in 0..20 {
        for n_quad in 1..20 {
            let mut qc = qc!(constant);
            (0..n_lin).for_each(|_| qc += ac.rand_scaled(rng));
            (0..n_quad).for_each(|_| qc += ac.rand_quad_scaled(rng));

            let mut qc0 = qc.clone();
            let mut qc1 = qc.clone();

            let u0 = qc.value();
            let u0 = &ac.assign(&u0);
            let u1 = &ac.eval(qc);

            u0.value()
                .zip(u1.value())
                .map(|(e0, e1)| assert_eq!(e0, e1));

            ac.equal(u0, u1).unwrap();

            qc0 -= u1;
            ac.zero_sum(qc0).unwrap();

            let negone: Value<_> = F::one().neg().into();
            qc1 += u0 * ac.var(&negone);
            ac.zero_sum(qc1).unwrap();
        }
    }
}

pub fn rand_synth_select_ir<F: Field>(ac: &mut AbstractCircuit<F>, rng: &mut impl RngCore) {
    let one = &ac.get_constant(F::one());
    let zero = &ac.get_constant(F::zero());

    let w0 = &ac.rand_var_assigned(rng);
    let w1 = &ac.rand_var_assigned(rng);
    let selected = &ac.select(one, w0, w1).unwrap();
    ac.equal(selected, w1).unwrap();
    let selected = &ac.select(zero, w0, w1).unwrap();
    ac.equal(selected, w0).unwrap();

    let x0 = F::rand(rng);
    let x1 = F::rand(rng);
    let w0 = &ac.get_constant(x0);
    let w1 = &ac.get_constant(x1);

    let selected = &ac.select_constant(one, x0, x1).unwrap();
    ac.equal(selected, w1).unwrap();
    let selected = &ac.select_constant(zero, x0, x1).unwrap();
    ac.equal(selected, w0).unwrap();

    let selected = &ac.select_or_constant(one, x0, w1).unwrap();
    ac.equal(selected, w1).unwrap();
    let selected = &ac.select_or_constant(zero, x0, w1).unwrap();
    ac.equal(selected, w0).unwrap();

    for table_size in 3..10 {
        let log_table_size = log2(table_size);
        let (table_constant, table_assigned): (Vec<_>, Vec<_>) = (0..table_size)
            .map(|_| {
                let e_constant = F::rand(rng);
                let e_assigned = ac.assign(&e_constant.into());
                (e_constant, e_assigned)
            })
            .unzip();

        for index in 0..table_size {
            let expect = &table_assigned[index];
            let index = ac.get_constant(F::from_u64(index as u64));
            let selector = ac
                .decompose_signed(1, log_table_size as usize, &index)
                .unwrap();
            let selected = &ac.select_from_table(&selector, &table_assigned).unwrap();
            ac.equal(selected, expect).unwrap();
            let selected = &ac
                .select_from_constant_table(&selector, &table_constant)
                .unwrap();
            ac.equal(selected, expect).unwrap();
        }

        // try with larger table
        let (table_constant, table_assigned): (Vec<_>, Vec<_>) = (0..table_size + 12)
            .map(|_| {
                let e_constant = F::rand(rng);
                let e_assigned = ac.assign(&e_constant.into());
                (e_constant, e_assigned)
            })
            .unzip();

        for index in 0..table_size {
            let expect = &table_assigned[index];
            let index = ac.get_constant(F::from_u64(index as u64));
            let selector = ac
                .decompose_signed(1, log_table_size as usize, &index)
                .unwrap();
            let selected = &ac.select_from_table(&selector, &table_assigned).unwrap();
            ac.equal(selected, expect).unwrap();
            let selected = &ac
                .select_from_constant_table(&selector, &table_constant)
                .unwrap();
            ac.equal(selected, expect).unwrap();
        }
    }
}

pub fn rand_synth_arithmetic_ir<F: Field>(ac: &mut AbstractCircuit<F>, rng: &mut impl RngCore) {
    let w0 = &ac.rand_var_assigned(rng);
    ac.equal(w0, w0).unwrap();

    let one = &ac.get_constant(F::one());
    let zero = &ac.get_constant(F::zero());
    ac.assert_one(one).unwrap();
    ac.assert_zero(zero).unwrap();
    ac.assert_bit(zero).unwrap();
    ac.assert_bit(one).unwrap();

    // equality
    {
        let w0 = &ac.rand_var_assigned(rng);
        ac.equal(w0, w0).unwrap();
        ac.assert_not_zero(w0).unwrap();

        let w1 = &ac.rand_var_assigned(rng);
        ac.assert_not_equal(w0, w1).unwrap();

        let must_be_one = ac.is_equal(w0, w0);
        ac.assert_one(&must_be_one).unwrap();

        let must_be_zero = ac.is_equal(w0, w1);
        ac.assert_zero(&must_be_zero).unwrap();
    }

    // constant registry
    {
        let c0 = F::rand(rng);
        let w0 = &ac.get_constant(c0);
        let w0_constant = &ac.get_constant(c0);
        ac.equal(w0_constant, w0).unwrap();
        ac.assert_equal_to_constant(w0, c0).unwrap();
    }

    // arithmetic
    {
        let x0 = F::rand(rng);
        let x1 = F::rand(rng);
        let w0 = &ac.assign(&x0.into());
        ac.assert_equal_to_constant(w0, x0).unwrap();
        let w1 = &ac.assign(&x1.into());
        ac.assert_equal_to_constant(w1, x1).unwrap();

        {
            // add
            let w0w1 = &ac.add(w0, w1);
            let w1w0 = &ac.add(w1, w0);
            ac.equal(w0w1, w1w0).unwrap();
            ac.assert_equal_to_constant(w0w1, x0 + x1).unwrap();
            let must_be_w0w1 = &ac.add_constant(w0, x1);
            ac.equal(must_be_w0w1, w0w1).unwrap();

            // sub
            let u = &ac.sub(w0, w1);
            ac.assert_equal_to_constant(u, x0 - x1).unwrap();
            let must_be_w0 = &ac.sub(w0w1, w1);
            let must_be_w1 = &ac.sub(w0w1, w0);
            ac.equal(must_be_w0, w0).unwrap();
            ac.equal(must_be_w1, w1).unwrap();
        }

        // mul
        {
            let w0w1 = &ac.mul(w0, w1);
            ac.assert_equal_to_constant(w0w1, x0 * x1).unwrap();
            let w1w0 = &ac.mul(w1, w0);
            ac.equal(w1w0, w0w1).unwrap();

            Scaled::new(w0, x1);
            let must_be_w0w1 = &ac.scale(&Scaled::new(w0, x1));
            ac.equal(must_be_w0w1, w0w1).unwrap();
            let must_be_w0w1 = &ac.scale(&Scaled::new(w1, x0));
            ac.equal(must_be_w0w1, w0w1).unwrap();

            // div
            let must_be_w1 = &ac.div_incomplete(w0w1, w0).unwrap();
            ac.equal(must_be_w1, w1).unwrap();
            let must_be_w0 = &ac.div_incomplete(w0w1, w1).unwrap();
            ac.equal(must_be_w0, w0).unwrap();

            // inv
            let inv_w0 = &ac.inv_incomplete(w0).unwrap();
            let must_be_one = &ac.mul(w0, inv_w0);
            ac.assert_one(must_be_one).unwrap();
            let (inv_w0, sign_must_be_zero) = &ac.inv(w0);
            let must_be_one = &ac.mul(w0, inv_w0);
            ac.assert_one(must_be_one).unwrap();
            ac.assert_zero(sign_must_be_zero).unwrap();
            let (result_must_be_one, sign_must_be_one) = &ac.inv(zero);
            ac.assert_one(sign_must_be_one).unwrap();
            ac.assert_one(result_must_be_one).unwrap();
        }
    }
}

pub fn rand_synth_memwo_ir<F: Field>(
    ac: &mut AbstractCircuit<F>,
    rng: &mut impl RngCore,
) -> Result<(), Error> {
    use super::mem::MemWriteOnceUnit;

    let tag = F::rand(rng);
    let mem_width = ac.wo_mem_ir.width().unwrap();

    let w0 = (0..mem_width).map(|_| ac.rand_var(rng)).collect::<Vec<_>>();
    let w1 = (0..mem_width).map(|_| ac.rand_var(rng)).collect::<Vec<_>>();
    let w2 = (0..mem_width).map(|_| ac.rand_var(rng)).collect::<Vec<_>>();
    let w3 = (0..mem_width).map(|_| ac.rand_var(rng)).collect::<Vec<_>>();

    let a0 = F::from_u64(0);
    let a1 = F::from_u64(1);
    let a2 = F::from_u64(2);
    let a3 = F::from_u64(3);

    ac.write(tag, a0, &w0).unwrap();
    ac.write(tag, a1, &w1).unwrap();
    ac.write(tag, a2, &w2).unwrap();
    ac.write(tag, a3, &w3).unwrap();

    let f0 = &ac.assign(&F::from_u64(0).into());
    let f1 = &ac.assign(&F::from_u64(1).into());
    let f2 = &ac.assign(&F::from_u64(2).into());
    let f3 = &ac.assign(&F::from_u64(3).into());

    let _w1 = ac.read(tag, F::zero(), f1).unwrap();
    w1.iter()
        .zip(_w1.iter())
        .try_for_each(|(w, a)| ac.equal(w, a))?;
    let _w0 = ac.read(tag, F::zero(), f0).unwrap();
    w0.iter()
        .zip(_w0.iter())
        .try_for_each(|(w, a)| ac.equal(w, a))?;
    let _w3 = ac.read(tag, F::zero(), f3).unwrap();
    w3.iter()
        .zip(_w3.iter())
        .try_for_each(|(w, a)| ac.equal(w, a))?;
    let _w3 = ac.read(tag, F::zero(), f3).unwrap();
    w3.iter()
        .zip(_w3.iter())
        .try_for_each(|(w, a)| ac.equal(w, a))?;
    let _w0 = ac.read(tag, F::zero(), f0).unwrap();
    w0.iter()
        .zip(_w0.iter())
        .try_for_each(|(w, a)| ac.equal(w, a))?;
    let _w2 = ac.read(tag, F::zero(), f2).unwrap();
    w2.iter()
        .zip(_w2.iter())
        .try_for_each(|(w, a)| ac.equal(w, a))?;
    let _w2 = ac.read(tag, F::zero(), f2).unwrap();
    w2.iter()
        .zip(_w2.iter())
        .try_for_each(|(w, a)| ac.equal(w, a))?;

    Ok(())
}

pub fn rand_synth_memro_ir<F: Field>(
    ac: &mut AbstractCircuit<F>,
    rng: &mut impl RngCore,
) -> Result<(), Error> {
    use super::mem::MemReadOnlyUnit;

    let tag = F::rand(rng);
    let mem_width = ac.ro_mem_ir.width().unwrap();

    let w0 = (0..mem_width).map(|_| F::rand(rng)).collect::<Vec<_>>();
    let w1 = (0..mem_width).map(|_| F::rand(rng)).collect::<Vec<_>>();
    let w2 = (0..mem_width).map(|_| F::rand(rng)).collect::<Vec<_>>();
    let w3 = (0..mem_width).map(|_| F::rand(rng)).collect::<Vec<_>>();

    let a0 = F::from_u64(0);
    let a1 = F::from_u64(1);
    let a2 = F::from_u64(2);
    let a3 = F::from_u64(3);

    ac.write(tag, a0, &w0).unwrap();
    ac.write(tag, a1, &w1).unwrap();
    ac.write(tag, a2, &w2).unwrap();
    ac.write(tag, a3, &w3).unwrap();

    let f0 = &ac.assign(&F::from_u64(0).into());
    let f1 = &ac.assign(&F::from_u64(1).into());
    let f2 = &ac.assign(&F::from_u64(2).into());
    let f3 = &ac.assign(&F::from_u64(3).into());

    let _w1 = ac.read(tag, F::zero(), f1).unwrap();
    w1.iter()
        .zip(_w1.iter())
        .try_for_each(|(a, w)| ac.assert_equal_to_constant(w, *a))?;
    let _w0 = ac.read(tag, F::zero(), f0).unwrap();
    w0.iter()
        .zip(_w0.iter())
        .try_for_each(|(a, w)| ac.assert_equal_to_constant(w, *a))?;
    let _w3 = ac.read(tag, F::zero(), f3).unwrap();
    w3.iter()
        .zip(_w3.iter())
        .try_for_each(|(a, w)| ac.assert_equal_to_constant(w, *a))?;
    let _w3 = ac.read(tag, F::zero(), f3).unwrap();
    w3.iter()
        .zip(_w3.iter())
        .try_for_each(|(a, w)| ac.assert_equal_to_constant(w, *a))?;
    let _w0 = ac.read(tag, F::zero(), f0).unwrap();
    w0.iter()
        .zip(_w0.iter())
        .try_for_each(|(a, w)| ac.assert_equal_to_constant(w, *a))?;
    let _w2 = ac.read(tag, F::zero(), f2).unwrap();
    w2.iter()
        .zip(_w2.iter())
        .try_for_each(|(a, w)| ac.assert_equal_to_constant(w, *a))?;
    let _w2 = ac.read(tag, F::zero(), f2).unwrap();
    w2.iter()
        .zip(_w2.iter())
        .try_for_each(|(a, w)| ac.assert_equal_to_constant(w, *a))?;

    Ok(())
}

pub fn rand_synth_bitwise<F: Field>(ac: &mut AbstractCircuit<F>, rng: &mut impl RngCore) {
    (0..100).for_each(|_| {
        let a: u8 = rng.gen();
        let a = F::from_u64(a as u64);
        let b: u8 = rng.gen();
        let b = F::from_u64(b as u64);
        let a = ac.assign(&a.into());
        let b = ac.assign(&b.into());
        let _ = ac.xor_word(&a, &b);
        let _ = ac.and_word(&a, &b);
    });
}

#[allow(dead_code)]
fn run_test_abstract_circuit<F: Field>() {
    use crate::utils::test::xor_rng;
    let rng = &mut xor_rng();

    let cfg = AbstractConfig::new(
        MemIRConfig::Active { width: 5 },
        MemIRConfig::Active { width: 5 },
        SelectIRConfig::default(),
        Pow5IRConfig::default(),
        BitwiseIRConfig::Lookup { num_bits: 8 },
        BitwiseIRConfig::Lookup { num_bits: 8 },
        true,
    );
    let ac = &mut AbstractCircuit::<F>::new(cfg);

    rand_synth_public_inputs_ir(ac, &[F::rand(rng).into()]);
    rand_synth_arithmetic_ir(ac, rng);
    rand_synth_select_ir(ac, rng);
    rand_synth_linear_combination_ir(ac, true, rng);
    rand_synth_quad_composions_ir(ac, true, rng);
    rand_synth_range_combinations_ir(ac, rng);
    rand_synth_memwo_ir(ac, rng).unwrap();
    rand_synth_memro_ir(ac, rng).unwrap();
    rand_synth_bitwise(ac, rng);
}

#[test]
#[cfg(any(feature = "arkworks", feature = "halo2", feature = "p3"))]
fn test_abstract_circuit() {
    #[cfg(feature = "arkworks")]
    use ark_bn254::Fr;
    #[cfg(feature = "halo2")]
    use halo2_proofs::halo2curves::bn256::Fr;
    #[cfg(feature = "p3")]
    use p3_goldilocks::Goldilocks as Fr;
    run_test_abstract_circuit::<Fr>();
}

// fn usage_example_1<F: Field>(a0: &Value<F>, a1: &Value<F>, b: &Value<F>) -> Result<(), Error> {
//     // new empty abstract circuit
//     let abc = &mut AbstractCircuit::<F>::default();

//     // assign variables as witnesses
//     let a0: Var<F> = abc.var(a0);
//     let a1: Var<F> = abc.var(a1);
//     let b: Var<F> = abc.var(b);

//     // use helper function for addition
//     let c0: Var<F> = abc.mul_add(&a0, &a1, &[b.into()]);

//     // or same can be achieved evaluating the expression
//     let qc = qc!(F::zero()) + a0 * a1 + b;
//     let c1: Var<F> = abc.eval(qc);

//     // two expressions should be equal
//     abc.equal(&c0, &c1)?;

//     Ok(())
// }

// fn usage_example_2<F: Field>(a0: &Var<F>) -> Result<(), Error> {
//     // new empty abstract circuit
//     let abc = &mut AbstractCircuit::<F>::default();

//     // * range a variable in 32 bits
//     // * and also get bytes as result of the decomposition
//     let bytes = abc.decompose(32, 8, a0)?;
//     let a1 = &abc.compose(&bytes, 8);

//     // round trip should be equal
//     abc.equal(a0, a1)?;

//     Ok(())
// }
