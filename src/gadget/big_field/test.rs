use super::crt::CrtGadget;
use super::crt_var::VarCrtGadget;
use super::num::{Big, Num, VarBig, VarNum};
use super::rns::{Range, Rns};
use crate::ir::ac::AbstractCircuit;
use crate::utils::log2;
use crate::utils::test::xor_rng;
use crate::{Error, Field, Value};
use itertools::{izip, Itertools};
use num_bigint::RandBigInt;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use rand::RngCore;
use std::ops::Neg;

pub fn rand_in_range(rng: &mut impl RngCore, signed: bool, ubound: &BigUint) -> BigInt {
    let ubound: &BigInt = &ubound.clone().into();
    let lbound = if signed { ubound.neg() } else { BigInt::zero() };
    rng.gen_bigint_range(&lbound, ubound)
}

impl<N: Field> Rns<N> {
    pub fn rand_in_range(&self, rng: &mut impl RngCore, signed: bool, ubound: &BigUint) -> Big<N> {
        let int = &rand_in_range(rng, signed, ubound);
        let big = self.big_from_int(int);
        self.validate_big(&big).unwrap();
        big
    }

    pub fn rand_in_rem(&self, rng: &mut impl RngCore) -> Big<N> {
        self.rand_in_range(rng, false, &self.max_rem)
    }

    pub fn rand_in_rem_signed(&self, rng: &mut impl RngCore) -> Big<N> {
        self.rand_in_range(rng, true, &self.max_rem)
    }

    pub fn rand_in_quot(&self, rng: &mut impl RngCore) -> Big<N> {
        self.rand_in_range(rng, true, &self.max_quot)
    }

    pub fn rand_in_op(&self, rng: &mut impl RngCore) -> Big<N> {
        self.rand_in_range(rng, false, &self.max_op)
    }

    pub fn rand_in_op_signed(&self, rng: &mut impl RngCore) -> Big<N> {
        self.rand_in_range(rng, true, &self.max_op)
    }

    pub fn rand_in_max(&self, rng: &mut impl RngCore) -> Big<N> {
        let limbs = self
            .max_unred_limbs
            .iter()
            .map(|max| rand_in_range(rng, false, max))
            .collect_vec();
        let big = self.big_from_limbs(&limbs);
        self.validate_big(&big).unwrap();
        big
    }

    pub fn rand_in_max_signed(&self, rng: &mut impl RngCore) -> Big<N> {
        let limbs = self
            .max_unred_limbs
            .iter()
            .map(|max| rand_in_range(rng, true, max))
            .collect_vec();
        let big = self.big_from_limbs(&limbs);
        self.validate_big(&big).unwrap();
        big
    }

    pub fn assign_overflown(&self, ac: &mut AbstractCircuit<N>, big: Value<&Big<N>>) -> VarBig<N> {
        let limbs = big.map(|big| big.limbs().to_vec());
        let limbs = limbs.transpose_vec(self.n_limbs());
        let limbs: Vec<_> = izip!(limbs, self.max_unred_limbs.iter())
            .map(|(limb, max)| {
                let var = ac.assign(&limb.as_ref().map(Num::nat));
                let int = limb.as_ref().map(Num::int);
                VarNum::overflow(&var, int, Some(max))
            })
            .collect();
        self.big_from_assigned_limbs(ac, &limbs, &self.max_unred_limbs.clone().into())
            .unwrap()
    }

    fn hint_mul(
        &self,
        w0: &VarBig<N>,
        w1: &VarBig<N>,
        d: &VarBig<N>,
        to_add: &[&VarBig<N>],
        to_sub: &[&VarBig<N>],
        p: Value<&BigInt>,
    ) -> Value<BigUint> {
        use num_integer::Integer;
        let w0 = w0.int();
        let w1 = w1.int();
        let d = d.int();

        let to_add = to_add.iter().map(|e| e.int().cloned()).collect_vec();
        let to_add: Value<Vec<_>> = Value::from_iter(to_add.to_vec());
        let to_add = to_add.map(|to_add| to_add.iter().sum::<BigInt>());

        let to_sub = to_sub.iter().map(|e| e.int().cloned()).collect_vec();
        let to_sub: Value<Vec<_>> = Value::from_iter(to_sub.to_vec());
        let to_sub = to_sub.map(|to_sub| to_sub.iter().sum::<BigInt>());

        // let p = self.wrong_mod().int();
        let d_inv = d.zip(p).map(|(d, p)| d.modinv(p).unwrap());
        let wide = d_inv * (w0 * w1 + to_add.as_ref() - to_sub.as_ref());

        wide.zip(p).map(|(wide, p)| {
            let (_, res) = wide.div_mod_floor(p);
            res.to_biguint().unwrap()
        })
    }
}

impl<N: Field> CrtGadget<N> {
    pub fn rand_in_field(&self, rng: &mut impl RngCore) -> Big<N> {
        self.rns.rand_in_range(rng, false, self.wrong_mod().uint())
    }

    pub fn rand_in_field_signed(&self, rng: &mut impl RngCore) -> Big<N> {
        self.rns.rand_in_range(rng, true, self.wrong_mod().uint())
    }

    pub fn neg_modulus(&self) -> Big<N> {
        self.wrong_mod.clone().neg()
    }

    pub fn minus_one_neg(&self) -> Big<N> {
        self.rns.big_from_int(&-BigInt::one())
    }

    pub fn minus_one_pos(&self) -> Big<N> {
        let minus_one = self.wrong_mod().uint() - BigUint::one();
        self.rns.big_from_uint(&minus_one)
    }

    fn hint_mul(
        &self,
        w0: &VarBig<N>,
        w1: &VarBig<N>,
        d: &VarBig<N>,
        to_add: &[&VarBig<N>],
        to_sub: &[&VarBig<N>],
    ) -> Value<BigUint> {
        self.rns
            .hint_mul(w0, w1, d, to_add, to_sub, self.wrong_mod().int().into())
    }
}

impl<N: Field> CrtGadget<N> {
    pub fn assign_rand_in_field(
        &self,
        ac: &mut AbstractCircuit<N>,
        rng: &mut impl RngCore,
    ) -> VarBig<N> {
        let big = self.rand_in_field(rng);
        let ret = self
            .assign(ac, big.uint().into(), &Range::Remainder)
            .unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_rand_in_rem(
        &self,
        ac: &mut AbstractCircuit<N>,
        rng: &mut impl RngCore,
    ) -> VarBig<N> {
        let big = self.rns.rand_in_rem(rng);
        let ret = self
            .assign(ac, big.uint().into(), &Range::Remainder)
            .unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_rand_in_rem_signed(
        &self,
        ac: &mut AbstractCircuit<N>,
        rng: &mut impl RngCore,
    ) -> VarBig<N> {
        let big = self.rns.rand_in_rem_signed(rng);
        let ret = self
            .assign_signed(ac, big.int().into(), &Range::Remainder)
            .unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_modulus(&self, ac: &mut AbstractCircuit<N>) -> VarBig<N> {
        let ret = self
            .assign(ac, self.wrong_mod.uint().into(), &Range::Remainder)
            .unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_neg_modulus(&self, ac: &mut AbstractCircuit<N>) -> VarBig<N> {
        let neg_mod = self.neg_modulus();
        let ret = self
            .assign_signed(ac, neg_mod.int().into(), &Range::Remainder)
            .unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_minus_one_neg(&self, ac: &mut AbstractCircuit<N>) -> VarBig<N> {
        let minus_one = self.minus_one_neg();
        let ret = self
            .assign_signed(ac, minus_one.int().into(), &Range::Remainder)
            .unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_minus_one_pos(&self, ac: &mut AbstractCircuit<N>) -> VarBig<N> {
        let minus_one = self.minus_one_pos();
        let ret = self
            .assign(ac, minus_one.uint().into(), &Range::Remainder)
            .unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_rand_in_quot(
        &self,
        ac: &mut AbstractCircuit<N>,
        rng: &mut impl RngCore,
    ) -> VarBig<N> {
        let big = self.rns.rand_in_quot(rng);
        let ret = self
            .assign_signed(ac, big.int().into(), &Range::Quotient)
            .unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_rand_in_op(
        &self,
        ac: &mut AbstractCircuit<N>,
        rng: &mut impl RngCore,
    ) -> VarBig<N> {
        let big = self.rns.rand_in_op(rng);
        let value = big.int().into();
        let range = big.limbs_uint().into();
        let ret = self.assign_signed(ac, value, &range).unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_rand_in_max(
        &self,
        ac: &mut AbstractCircuit<N>,
        rng: &mut impl RngCore,
    ) -> VarBig<N> {
        let big = &self.rns.rand_in_max(rng);
        self.rns.validate_big(big).unwrap();
        let ret = self.rns.assign_overflown(ac, big.into());
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_rand_in_max_signed(
        &self,
        ac: &mut AbstractCircuit<N>,
        rng: &mut impl RngCore,
    ) -> VarBig<N> {
        let big = &self.rns.rand_in_max(rng);
        let ret = self.rns.assign_overflown(ac, big.into());
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }
}

pub fn crt_garget_test<N: Field>(
    ac: &mut AbstractCircuit<N>,
    rng: &mut impl RngCore,
    wrong_mod: &BigUint,
    limb_size: usize,
    sublimb_size: usize,
) {
    let crt = CrtGadget::<N>::new(limb_size, sublimb_size, wrong_mod);
    let rns = crt.rns();

    let equal_normal =
        |ac: &mut AbstractCircuit<N>, u0: &VarBig<N>, u1: &VarBig<N>| -> Result<(), Error> {
            rns.validate_varbig(u0)?;
            rns.validate_varbig(u1)?;
            {
                let dif = u0.int() - u1.int();
                dif.map(|u| assert_eq!(u % crt.wrong_mod.int(), BigInt::zero()));
            }
            crt.normal_equal(ac, u0, u1)?;
            crt.normal_equal(ac, u1, u0)?;
            Ok(())
        };

    let equal_strict =
        |ac: &mut AbstractCircuit<N>, u0: &VarBig<N>, u1: &VarBig<N>| -> Result<(), Error> {
            equal_normal(ac, u0, u1)?;
            u0.int()
                .zip(u1.int())
                .maybe(|(u0, u1)| (u0 == u1).then_some(()))?;
            u0.copy_equal(ac, u1)?;
            u1.copy_equal(ac, u0)?;
            Ok(())
        };

    let equal_strict_in_field =
        |ac: &mut AbstractCircuit<N>, u0: &VarBig<N>, u1: &VarBig<N>| -> Result<(), Error> {
            equal_strict(ac, u0, u1)?;
            u0.big().zip(u1.big()).map(|(u0, u1)| {
                assert!(!u0.is_negative());
                assert!(!u1.is_negative());
                assert!(u0.int() < crt.wrong_mod.int());
                assert!(u1.int() < crt.wrong_mod.int());
            });
            crt.assert_in_field(ac, u0)?;
            crt.assert_in_field(ac, u1)?;
            Ok(())
        };

    {
        let a0 = &crt.assign_rand_in_field(ac, rng);
        let a1 = &crt.reduce(ac, a0);
        equal_strict_in_field(ac, a0, a1).unwrap();

        let a0 = &crt.assign_rand_in_rem(ac, rng);
        let a1 = &crt.reduce(ac, a0);
        equal_normal(ac, a0, a1).unwrap();

        let a0 = &crt.assign_rand_in_op(ac, rng);
        let a1 = &crt.reduce(ac, a0);
        equal_normal(ac, a0, a1).unwrap();

        let a0 = &crt.assign_rand_in_quot(ac, rng);
        let a1 = &crt.reduce(ac, a0);
        equal_normal(ac, a0, a1).unwrap();

        let a0 = &crt.assign_rand_in_max(ac, rng);
        let a1 = &crt.reduce(ac, a0);
        equal_normal(ac, a0, a1).unwrap();

        let a0 = &crt.assign_rand_in_rem_signed(ac, rng);
        let a1 = &crt.reduce(ac, a0);
        equal_normal(ac, a0, a1).unwrap();

        let a0 = &crt.assign_rand_in_max_signed(ac, rng);
        let a1 = &crt.reduce(ac, a0);
        equal_normal(ac, a0, a1).unwrap();
    }

    {
        let t0 = ac.get_log("big-field-forced-red");
        let a0 = crt.assign_rand_in_rem_signed(ac, rng);
        let mut u0 = a0.clone();
        let mut n_lazy_double = 0u64;
        loop {
            crt.reduce_operand(ac, &u0);
            let t1 = ac.get_log("big-field-forced-red");
            if t1 > t0 {
                break;
            }
            n_lazy_double += 1;
            u0 = u0.double(ac);
        }
        println!("n_lazy_double: {}", n_lazy_double);
        let s = BigUint::one() << n_lazy_double;
        let s = crt.assign(ac, (&s).into(), &Range::Remainder).unwrap();

        let u1 = crt.mul(ac, &a0, &s, &[], &[]);

        equal_normal(ac, &u0, &u1).unwrap();
    }

    let zero = &crt.get_constant(ac, &BigUint::zero()).unwrap();
    let one = &crt.get_constant(ac, &BigUint::one()).unwrap();
    let p = &crt.assign_modulus(ac);
    let minus_one_neg = &crt.assign_minus_one_neg(ac);
    let minus_one_pos = &crt.assign_minus_one_pos(ac);
    let neg_p = &crt.assign_neg_modulus(ac);

    {
        let test_into_bytes = |ac: &mut AbstractCircuit<N>, a: &VarBig<N>| {
            let expected_bytes = a.uint().map(|a| {
                let mut bytes = vec![0u8; rns.number_of_bytes()];
                bytes
                    .iter_mut()
                    .zip(a.to_bytes_le())
                    .for_each(|(dst, src)| *dst = src);
                bytes
            });
            let var_bytes = crt.into_bytes(ac, a);
            assert_eq!(var_bytes.len(), rns.number_of_bytes());
            var_bytes.iter().enumerate().for_each(|(i, byte)| {
                let expected = expected_bytes.as_ref().map(|b| b[i]);
                byte.value()
                    .zip(expected)
                    .map(|(byte, expected)| assert_eq!(byte, expected));
            });
        };
        let a0 = &crt.assign_rand_in_rem(ac, rng);
        test_into_bytes(ac, zero);
        test_into_bytes(ac, one);
        test_into_bytes(ac, a0);
    }

    let y = &p.sub(ac, one);
    equal_normal(ac, minus_one_neg, minus_one_pos).unwrap();
    equal_strict_in_field(ac, y, minus_one_pos).unwrap();
    crt.assert_in_field(ac, minus_one_pos).unwrap();

    {
        crt.assert_in_field(ac, zero).unwrap();
        let must_be_true = crt.is_zero(ac, zero);
        ac.assert_one(&must_be_true).unwrap();
        let must_be_false = crt.is_one(ac, zero);
        ac.assert_zero(&must_be_false).unwrap();
        crt.assert_zero(ac, zero).unwrap();
        let _zero = &crt.neg(ac, zero);
        crt.assert_zero(ac, _zero).unwrap();

        crt.assert_in_field(ac, one).unwrap();
        let must_be_true = crt.is_one(ac, one);
        ac.assert_one(&must_be_true).unwrap();
        crt.assert_not_zero(ac, one).unwrap();
        let must_be_false = crt.is_zero(ac, one);
        ac.assert_zero(&must_be_false).unwrap();
        crt.assert_not_equal(ac, one, zero).unwrap();

        crt.assert_zero(ac, p).unwrap();
        let must_be_true = crt.is_zero(ac, p);
        ac.assert_one(&must_be_true).unwrap();
        let must_be_true = crt.is_equal(ac, zero, p);
        ac.assert_one(&must_be_true).unwrap();
        let p_neg = &crt.neg(ac, p);
        crt.assert_zero(ac, p_neg).unwrap();

        let a0 = &crt.assign_rand_in_rem_signed(ac, rng);
        let a1 = &crt.assign_rand_in_rem_signed(ac, rng);
        crt.assert_not_equal(ac, a0, a1).unwrap();
        let must_be_false = &crt.is_equal(ac, a0, a1);
        ac.assert_zero(must_be_false).unwrap();
        let must_be_true = &crt.is_equal(ac, a0, a0);
        ac.assert_one(must_be_true).unwrap();

        for _ in 0..10 {
            let a0 = &crt.assign_rand_in_field(ac, rng);
            crt.assert_in_field(ac, a0).unwrap();
        }
    }

    // a == a'
    let v0 = &crt.assign_rand_in_field(ac, rng);
    let v1 = &crt.reduce(ac, v0);
    equal_strict_in_field(ac, v0, v1).unwrap();

    // a == a + modulus
    let v1 = &v0.add(ac, p);
    equal_normal(ac, v0, v1).unwrap();
    let v1 = &crt.reduce(ac, v0);
    equal_strict_in_field(ac, v0, v1).unwrap();

    // a == a - modulus
    let v1 = &v0.sub(ac, p);
    equal_normal(ac, v1, v0).unwrap();
    let v1 = &crt.reduce(ac, v0);
    equal_strict_in_field(ac, v1, v0).unwrap();

    // 0 == modulus
    equal_normal(ac, p, zero).unwrap();
    let must_be_zero = crt.reduce(ac, p);
    equal_strict_in_field(ac, zero, &must_be_zero).unwrap();

    // 0 == a - a
    {
        let a0 = &rns.rand_in_rem(rng);
        let a1 = a0.neg();
        let v0 = &crt
            .assign_signed(ac, a0.int().into(), &Range::Remainder)
            .unwrap();
        let v1 = &crt
            .assign_signed(ac, a1.int().into(), &Range::Remainder)
            .unwrap();
        let v1 = v1.add(ac, v0);
        equal_strict(ac, &v1, zero).unwrap();
    }

    // 0 == (-a) + a
    let a0 = &crt.assign_rand_in_rem(ac, rng);
    let a1 = &crt.neg(ac, a0);
    let must_be_p = a0.add(ac, a1);
    crt.assert_zero(ac, &must_be_p).unwrap();
    equal_strict(ac, p, &must_be_p).unwrap();

    // a == a'
    let v0 = &crt.assign_rand_in_max(ac, rng);
    let v1 = &crt.reduce(ac, v0);
    equal_normal(ac, v0, v1).unwrap();

    // 0 == 0 - p
    let must_be_zero = zero.sub(ac, p);
    crt.assert_zero(ac, &must_be_zero).unwrap();
    equal_normal(ac, zero, &must_be_zero).unwrap();
    let must_be_zero = crt.reduce(ac, &must_be_zero);
    crt.assert_zero(ac, &must_be_zero).unwrap();
    equal_strict_in_field(ac, zero, &must_be_zero).unwrap();

    // -1 == p - 1
    let _neg_one = p.sub(ac, one);
    equal_normal(ac, minus_one_neg, &_neg_one).unwrap();
    // 0 == 1 - 1
    let must_be_zero = minus_one_neg.add(ac, one);
    equal_strict_in_field(ac, zero, &must_be_zero).unwrap();
    // 1 == p + 1
    let _one = p.add(ac, one);
    equal_normal(ac, &_one, one).unwrap();
    let _one = crt.reduce(ac, one);
    equal_strict_in_field(ac, one, &_one).unwrap();

    {
        let a = &crt.assign_rand_in_rem(ac, rng);
        let a_red = &crt.reduce(ac, a);
        let x = &crt.assign_rand_in_rem(ac, rng);
        let neg_x = &crt.neg(ac, x);

        let c = &crt.mul(ac, a, zero, &[p, minus_one_neg, one], &[]);
        crt.assert_zero(ac, c).unwrap();
        equal_strict_in_field(ac, c, zero).unwrap();

        let c = &crt.mul(ac, a, p, &[x], &[x, p, minus_one_neg, one]);
        crt.assert_zero(ac, c).unwrap();
        equal_strict_in_field(ac, c, zero).unwrap();

        let c = &crt.mul(ac, a, neg_p, &[x, zero], &[x, p]);
        crt.assert_zero(ac, c).unwrap();
        equal_strict_in_field(ac, c, zero).unwrap();

        let c = &crt.mul(ac, a, one, &[x, neg_x], &[one, minus_one_neg]);
        equal_strict_in_field(ac, c, a_red).unwrap();

        let c = &crt.mul(ac, a, minus_one_neg, &[x, one, p], &[zero, x, one, neg_p]);
        let c = &c.add(ac, a);
        crt.assert_zero(ac, c).unwrap();
        equal_normal(ac, c, zero).unwrap();

        let c = &crt.mul(
            ac,
            minus_one_pos,
            minus_one_neg,
            &[one, p, neg_p],
            &[zero, one],
        );
        equal_strict_in_field(ac, c, one).unwrap();

        let c = &crt.mul(ac, minus_one_neg, one, &[], &[]);
        equal_normal(ac, c, minus_one_neg).unwrap();

        for _ in 0..10 {
            let a = &crt.assign_rand_in_rem_signed(ac, rng);
            let b_constant = rns.rand_in_rem(rng);
            let b = &crt
                .assign(ac, b_constant.uint().into(), &Range::Remainder)
                .unwrap();
            let to_add = (0..3)
                .map(|_| crt.assign_rand_in_max_signed(ac, rng))
                .collect_vec();
            let to_add = to_add.iter().collect_vec();
            let c0 = &crt.mul(ac, a, b, &to_add, &to_add);
            let c1 = crt.hint_mul(a, b, one, &to_add, &to_add);
            let c1 = &crt.assign(ac, c1.as_ref(), &Range::Remainder).unwrap();
            equal_strict_in_field(ac, c0, c1).unwrap();
            let c2 = &crt.mul_constant(ac, a, &b_constant, &to_add, &to_add);
            equal_strict_in_field(ac, c0, c2).unwrap();

            let c0 = &crt.square(ac, a, &to_add, &to_add);
            let c1 = crt.hint_mul(a, a, one, &to_add, &to_add);
            let c1 = &crt.assign(ac, c1.as_ref(), &Range::Remainder).unwrap();
            equal_strict_in_field(ac, c0, c1).unwrap();
        }

        {
            let a = &crt.assign_rand_in_op(ac, rng);
            let b = &crt.assign_rand_in_op(ac, rng);
            let neg_a = &crt.neg(ac, a);
            let c = &crt.div(ac, a, one);
            equal_normal(ac, c, a).unwrap();
            let c = &crt.div(ac, a, minus_one_neg);
            equal_normal(ac, c, neg_a).unwrap();
            let ab = &crt.div(ac, a, b);
            let c = &crt.mul(ac, ab, b, &[], &[]);
            equal_normal(ac, a, c).unwrap();
        }

        {
            let a = &crt.assign_rand_in_rem_signed(ac, rng);
            let x = &crt.assign_rand_in_rem_signed(ac, rng);
            let neg_a = &crt.neg(ac, a);
            let neg_x = &crt.neg(ac, x);

            let c = &crt.mul_div(ac, a, one, one, &[], &[]);
            equal_normal(ac, a, c).unwrap();
            let c = &crt.mul_div(ac, a, one, minus_one_neg, &[], &[]);
            equal_normal(ac, neg_a, c).unwrap();
            let c = &crt.mul_div(ac, a, one, a, &[], &[]);
            equal_normal(ac, one, c).unwrap();
            let c = &crt.mul_div(ac, a, a, a, &[], &[]);
            equal_normal(ac, a, c).unwrap();
            let c = &crt.mul_div(ac, a, a, neg_a, &[], &[]);
            equal_normal(ac, neg_a, c).unwrap();
            let c = &crt.mul_div(ac, a, neg_a, neg_a, &[], &[]);
            equal_normal(ac, a, c).unwrap();
            let c = &crt.mul_div(ac, a, x, neg_x, &[], &[]);
            equal_normal(ac, neg_a, c).unwrap();
            let c = &crt.mul_div(ac, zero, x, a, &[a], &[]);
            equal_normal(ac, one, c).unwrap();
        }

        for _ in 0..10 {
            let a = &crt.assign_rand_in_rem_signed(ac, rng);
            let b = &crt.assign_rand_in_rem_signed(ac, rng);
            let d = &crt.assign_rand_in_rem_signed(ac, rng);
            let to_add = (0..3)
                .map(|_| crt.assign_rand_in_max_signed(ac, rng))
                .collect_vec();
            let to_add = to_add.iter().collect_vec();
            let c0 = &crt.mul_div(ac, a, b, d, &to_add, &to_add);
            let c1 = crt.hint_mul(a, b, d, &to_add, &to_add);
            let c1 = &crt.assign(ac, c1.as_ref(), &Range::Remainder).unwrap();
            equal_normal(ac, c0, c1).unwrap();
        }
    }

    {
        for table_size in 3..10 {
            let log_table_size = log2(table_size);
            let table = (0..table_size)
                .map(|_| crt.assign_rand_in_rem(ac, rng))
                .collect_vec();

            for index in 0..table_size {
                let expect = &table[index];
                let index = ac.get_constant(N::from_u64(index as u64));
                let selector = ac.decompose(1, log_table_size as usize, &index).unwrap();
                let selected = &crt.select_from_table(ac, &selector, &table).unwrap();
                equal_strict(ac, expect, selected).unwrap();
            }

            // try with larger table
            let table = (0..table_size + 10)
                .map(|_| crt.assign_rand_in_rem(ac, rng))
                .collect_vec();

            for index in 0..table_size {
                let expect = &table[index];
                let index = ac.get_constant(N::from_u64(index as u64));
                let selector = ac.decompose(1, log_table_size as usize, &index).unwrap();
                let selected = &crt.select_from_table(ac, &selector, &table).unwrap();
                equal_strict(ac, expect, selected).unwrap();
            }
        }
    }
}

#[allow(dead_code)]
fn run_crt_gadget_test<N: Field>() {
    use num_traits::Num;

    fn run<N: Field>(modulus: &str) {
        let mut rng = xor_rng();
        let mut ac = AbstractCircuit::<N>::default();
        ac.switch_sanity_check(true);
        let wrong_mod = BigUint::from_str_radix(modulus, 10).unwrap();
        let limb_size = 90;
        let sublimb_size = 15;
        crt_garget_test(&mut ac, &mut rng, &wrong_mod, limb_size, sublimb_size);
        // test_bug(&mut ac, &mut rng, &rns, sublimb_size);
    }

    // BN base field modulus
    run::<N>("21888242871839275222246405745257275088696311157297823662689037894645226208583");
    // BLS base field modulus
    run::<N>("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787");
    // BW6 base field modulus
    run::<N>("6891450384315732539396789682275657542479668912536150109513790160209623422243491736087683183289411687640864567753786613451161759120554247759349511699125301598951605099378508850372543631423596795951899700429969112842764913119068299");
    // 2048 RSA modulus
    run::<N>("25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357");
}

impl<N: Field> VarCrtGadget<N> {
    pub fn rand_in_field(&self, rng: &mut impl RngCore) -> Value<Big<N>> {
        self.wrong_mod()
            .uint()
            .map(|wrong_mod| self.rns.rand_in_range(rng, false, wrong_mod))
    }

    pub fn rand_in_field_signed(&self, rng: &mut impl RngCore) -> Value<Big<N>> {
        self.wrong_mod()
            .uint()
            .map(|wrong_mod| self.rns.rand_in_range(rng, true, wrong_mod))
    }

    pub fn neg_modulus(&self) -> Value<Big<N>> {
        self.wrong_mod()
            .big()
            .map(|wrong_mod| wrong_mod.clone().neg())
    }

    pub fn minus_one_neg(&self) -> Big<N> {
        self.rns.big_from_int(&-BigInt::one())
    }

    pub fn minus_one_pos(&self) -> Value<Big<N>> {
        self.wrong_mod().uint().map(|wrong_mod| {
            let minus_one = wrong_mod - 1usize;
            self.rns.big_from_uint(&minus_one)
        })
    }

    fn hint_mul(
        &self,
        w0: &VarBig<N>,
        w1: &VarBig<N>,
        d: &VarBig<N>,
        to_add: &[&VarBig<N>],
        to_sub: &[&VarBig<N>],
    ) -> Value<BigUint> {
        self.rns
            .hint_mul(w0, w1, d, to_add, to_sub, self.wrong_mod().int())
    }
}

impl<N: Field> VarCrtGadget<N> {
    pub fn assign_overflown(&self, ac: &mut AbstractCircuit<N>, big: Value<&Big<N>>) -> VarBig<N> {
        let limbs = big.map(|big| big.limbs().to_vec());
        let limbs = limbs.transpose_vec(self.rns.n_limbs());
        let limbs: Vec<_> = izip!(limbs, self.rns.max_unred_limbs.iter())
            .map(|(limb, max)| {
                let var = ac.assign(&limb.as_ref().map(Num::nat));
                let int = limb.as_ref().map(Num::int);
                VarNum::overflow(&var, int, Some(max))
            })
            .collect();
        self.rns
            .big_from_assigned_limbs(ac, &limbs, &self.rns.max_unred_limbs.clone().into())
            .unwrap()
    }

    pub fn assign_rand_in_field(
        &self,
        ac: &mut AbstractCircuit<N>,
        rng: &mut impl RngCore,
    ) -> VarBig<N> {
        let big = self.rand_in_field(rng);
        let big = big.as_ref().map(Big::uint);
        let ret = self.assign(ac, big, &Range::Remainder).unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_rand_in_rem(
        &self,
        ac: &mut AbstractCircuit<N>,
        rng: &mut impl RngCore,
    ) -> VarBig<N> {
        let big = self.rns.rand_in_rem(rng);
        let ret = self
            .assign(ac, big.uint().into(), &Range::Remainder)
            .unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_rand_in_rem_signed(
        &self,
        ac: &mut AbstractCircuit<N>,
        rng: &mut impl RngCore,
    ) -> VarBig<N> {
        let big = self.rns.rand_in_rem_signed(rng);
        let ret = self
            .assign_signed(ac, big.int().into(), &Range::Remainder)
            .unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_modulus(&self, ac: &mut AbstractCircuit<N>) -> VarBig<N> {
        let ret = self
            .assign(ac, self.wrong_mod.uint(), &Range::Remainder)
            .unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_neg_modulus(&self, ac: &mut AbstractCircuit<N>) -> VarBig<N> {
        let neg_mod = self.neg_modulus();
        let neg_mod = neg_mod.as_ref().map(Big::int);
        let ret = self.assign_signed(ac, neg_mod, &Range::Remainder).unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_minus_one_neg(&self, ac: &mut AbstractCircuit<N>) -> VarBig<N> {
        let minus_one = self.minus_one_neg();
        let ret = self
            .assign_signed(ac, minus_one.int().into(), &Range::Remainder)
            .unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_minus_one_pos(&self, ac: &mut AbstractCircuit<N>) -> VarBig<N> {
        let minus_one = self.minus_one_pos();
        let minus_one = minus_one.as_ref().map(Big::uint);
        let ret = self.assign(ac, minus_one, &Range::Remainder).unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_rand_in_quot(
        &self,
        ac: &mut AbstractCircuit<N>,
        rng: &mut impl RngCore,
    ) -> VarBig<N> {
        let big = self.rns.rand_in_quot(rng);
        let ret = self
            .assign_signed(ac, big.int().into(), &Range::Quotient)
            .unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_rand_in_op(
        &self,
        ac: &mut AbstractCircuit<N>,
        rng: &mut impl RngCore,
    ) -> VarBig<N> {
        let big = self.rns.rand_in_op(rng);
        let value = big.int().into();
        let range = big.limbs_uint().into();
        let ret = self.assign_signed(ac, value, &range).unwrap();
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_rand_in_max(
        &self,
        ac: &mut AbstractCircuit<N>,
        rng: &mut impl RngCore,
    ) -> VarBig<N> {
        let big = &self.rns.rand_in_max(rng);
        self.rns.validate_big(big).unwrap();
        let ret = self.assign_overflown(ac, big.into());
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }

    pub fn assign_rand_in_max_signed(
        &self,
        ac: &mut AbstractCircuit<N>,
        rng: &mut impl RngCore,
    ) -> VarBig<N> {
        let big = &self.rns.rand_in_max(rng);
        let ret = self.assign_overflown(ac, big.into());
        self.rns.validate_varbig(&ret).unwrap();
        ret
    }
}

pub fn var_crt_garget_test<N: Field>(
    ac: &mut AbstractCircuit<N>,
    rng: &mut impl RngCore,
    wrong_mod: Value<&BigUint>,
    mod_size: usize,
    limb_size: usize,
    sublimb_size: usize,
) {
    let crt = VarCrtGadget::<N>::new(ac, mod_size, limb_size, sublimb_size, wrong_mod).unwrap();
    let rns = crt.rns();

    let equal_normal =
        |ac: &mut AbstractCircuit<N>, u0: &VarBig<N>, u1: &VarBig<N>| -> Result<(), Error> {
            rns.validate_varbig(u0)?;
            rns.validate_varbig(u1)?;
            {
                let dif = u0.int() - u1.int();
                let p = crt.wrong_mod.int();
                dif.zip(p).map(|(u, p)| assert_eq!(u % p, BigInt::zero()));
            }
            crt.normal_equal(ac, u0, u1)?;
            crt.normal_equal(ac, u1, u0)?;
            Ok(())
        };

    let equal_strict =
        |ac: &mut AbstractCircuit<N>, u0: &VarBig<N>, u1: &VarBig<N>| -> Result<(), Error> {
            equal_normal(ac, u0, u1)?;
            u0.int()
                .zip(u1.int())
                .maybe(|(u0, u1)| (u0 == u1).then_some(()))?;
            u0.copy_equal(ac, u1)?;
            u1.copy_equal(ac, u0)?;
            Ok(())
        };

    let equal_strict_in_field =
        |ac: &mut AbstractCircuit<N>, u0: &VarBig<N>, u1: &VarBig<N>| -> Result<(), Error> {
            equal_strict(ac, u0, u1)?;
            u0.big().zip(u1.big()).map(|(u0, u1)| {
                assert!(!u0.is_negative());
                assert!(!u1.is_negative());
                // assert!(u0.int() < crt.wrong_mod.int());
                // assert!(u1.int() < crt.wrong_mod.int());
            });
            crt.assert_in_field(ac, u0)?;
            crt.assert_in_field(ac, u1)?;
            Ok(())
        };

    {
        let a0 = &crt.assign_rand_in_field(ac, rng);
        let a1 = &crt.reduce(ac, a0);
        equal_strict_in_field(ac, a0, a1).unwrap();

        let a0 = &crt.assign_rand_in_rem(ac, rng);
        let a1 = &crt.reduce(ac, a0);
        equal_normal(ac, a0, a1).unwrap();

        let a0 = &crt.assign_rand_in_op(ac, rng);
        let a1 = &crt.reduce(ac, a0);
        equal_normal(ac, a0, a1).unwrap();

        let a0 = &crt.assign_rand_in_quot(ac, rng);
        let a1 = &crt.reduce(ac, a0);
        equal_normal(ac, a0, a1).unwrap();

        let a0 = &crt.assign_rand_in_max(ac, rng);
        let a1 = &crt.reduce(ac, a0);
        equal_normal(ac, a0, a1).unwrap();

        let a0 = &crt.assign_rand_in_rem_signed(ac, rng);
        let a1 = &crt.reduce(ac, a0);
        equal_normal(ac, a0, a1).unwrap();

        let a0 = &crt.assign_rand_in_max_signed(ac, rng);

        let a1 = &crt.reduce(ac, a0);
        equal_normal(ac, a0, a1).unwrap();
    }

    {
        let t0 = ac.get_log("big-field-forced-red");
        let a0 = crt.assign_rand_in_rem_signed(ac, rng);
        let mut u0 = a0.clone();
        let mut n_lazy_double = 0u64;
        loop {
            crt.reduce_operand(ac, &u0);
            let t1 = ac.get_log("big-field-forced-red");
            if t1 > t0 {
                break;
            }
            n_lazy_double += 1;
            u0 = u0.double(ac);
        }
        println!("n_lazy_double: {}", n_lazy_double);
        let s = BigUint::one() << n_lazy_double;
        let s = crt.assign(ac, (&s).into(), &Range::Remainder).unwrap();

        let u1 = crt.mul(ac, &a0, &s, &[], &[]);

        equal_normal(ac, &u0, &u1).unwrap();
    }

    let zero = &crt.get_constant(ac, &BigUint::zero()).unwrap();
    let one = &crt.get_constant(ac, &BigUint::one()).unwrap();
    let p = &crt.assign_modulus(ac);
    let minus_one_neg = &crt.assign_minus_one_neg(ac);
    let minus_one_pos = &crt.assign_minus_one_pos(ac);
    let neg_p = &crt.assign_neg_modulus(ac);

    {
        let test_into_bytes = |ac: &mut AbstractCircuit<N>, a: &VarBig<N>| {
            let expected_bytes = a.uint().map(|a| {
                let mut bytes = vec![0u8; rns.number_of_bytes()];
                bytes
                    .iter_mut()
                    .zip(a.to_bytes_le())
                    .for_each(|(dst, src)| *dst = src);
                bytes
            });
            let var_bytes = crt.to_bytes(ac, a);
            assert_eq!(var_bytes.len(), rns.number_of_bytes());
            var_bytes.iter().enumerate().for_each(|(i, byte)| {
                let expected = expected_bytes.as_ref().map(|b| b[i]);
                byte.value()
                    .zip(expected)
                    .map(|(byte, expected)| assert_eq!(byte, expected));
            });
        };
        let a0 = &crt.assign_rand_in_rem(ac, rng);
        test_into_bytes(ac, zero);
        test_into_bytes(ac, one);
        test_into_bytes(ac, a0);
    }

    {
        crt.assert_in_field(ac, zero).unwrap();
        let must_be_true = crt.is_zero(ac, zero);
        ac.assert_one(&must_be_true).unwrap();
        let must_be_false = crt.is_one(ac, zero);
        ac.assert_zero(&must_be_false).unwrap();
        crt.assert_zero(ac, zero).unwrap();
        let _zero = &crt.neg(ac, zero);
        crt.assert_zero(ac, _zero).unwrap();

        crt.assert_in_field(ac, one).unwrap();
        let must_be_true = crt.is_one(ac, one);
        ac.assert_one(&must_be_true).unwrap();
        crt.assert_not_zero(ac, one).unwrap();
        let must_be_false = crt.is_zero(ac, one);
        ac.assert_zero(&must_be_false).unwrap();
        crt.assert_not_equal(ac, one, zero).unwrap();

        crt.assert_zero(ac, p).unwrap();
        let must_be_true = crt.is_zero(ac, p);
        ac.assert_one(&must_be_true).unwrap();
        let must_be_true = crt.is_equal(ac, zero, p);
        ac.assert_one(&must_be_true).unwrap();
        let p_neg = &crt.neg(ac, p);
        crt.assert_zero(ac, p_neg).unwrap();

        let a0 = &crt.assign_rand_in_rem_signed(ac, rng);
        let a1 = &crt.assign_rand_in_rem_signed(ac, rng);
        crt.assert_not_equal(ac, a0, a1).unwrap();
        let must_be_false = &crt.is_equal(ac, a0, a1);
        ac.assert_zero(must_be_false).unwrap();
        let must_be_true = &crt.is_equal(ac, a0, a0);
        ac.assert_one(must_be_true).unwrap();

        for _ in 0..10 {
            let a0 = &crt.assign_rand_in_field(ac, rng);
            crt.assert_in_field(ac, a0).unwrap();
        }
    }

    // a == a'
    let v0 = &crt.assign_rand_in_field(ac, rng);
    let v1 = &crt.reduce(ac, v0);
    equal_strict_in_field(ac, v0, v1).unwrap();

    // a == a + modulus
    let v1 = &v0.add(ac, p);
    equal_normal(ac, v0, v1).unwrap();
    let v1 = &crt.reduce(ac, v0);
    equal_strict_in_field(ac, v0, v1).unwrap();

    // a == a - modulus
    let v1 = &v0.sub(ac, p);
    equal_normal(ac, v1, v0).unwrap();
    let v1 = &crt.reduce(ac, v0);
    equal_strict_in_field(ac, v1, v0).unwrap();

    // 0 == modulus
    equal_normal(ac, p, zero).unwrap();
    let must_be_zero = crt.reduce(ac, p);
    equal_strict_in_field(ac, zero, &must_be_zero).unwrap();

    // 0 == a - a
    {
        let a0 = &rns.rand_in_rem(rng);
        let a1 = a0.neg();
        let v0 = &crt
            .assign_signed(ac, a0.int().into(), &Range::Remainder)
            .unwrap();
        let v1 = &crt
            .assign_signed(ac, a1.int().into(), &Range::Remainder)
            .unwrap();
        let v1 = v1.add(ac, v0);
        equal_strict(ac, &v1, zero).unwrap();
    }

    // 0 == (-a) + a
    let a0 = &crt.assign_rand_in_rem(ac, rng);
    let a1 = &crt.neg(ac, a0);
    let must_be_p = a0.add(ac, a1);
    crt.assert_zero(ac, &must_be_p).unwrap();
    equal_strict(ac, p, &must_be_p).unwrap();

    // a == a'
    let v0 = &crt.assign_rand_in_max(ac, rng);
    let v1 = &crt.reduce(ac, v0);
    equal_normal(ac, v0, v1).unwrap();

    // 0 == 0 - p
    let must_be_zero = zero.sub(ac, p);
    crt.assert_zero(ac, &must_be_zero).unwrap();
    equal_normal(ac, zero, &must_be_zero).unwrap();
    let must_be_zero = crt.reduce(ac, &must_be_zero);
    crt.assert_zero(ac, &must_be_zero).unwrap();
    equal_strict_in_field(ac, zero, &must_be_zero).unwrap();

    // -1 == p - 1
    let _neg_one = p.sub(ac, one);
    equal_normal(ac, minus_one_neg, &_neg_one).unwrap();
    // 0 == 1 - 1
    let must_be_zero = minus_one_neg.add(ac, one);
    equal_strict_in_field(ac, zero, &must_be_zero).unwrap();
    // 1 == p + 1
    let _one = p.add(ac, one);
    equal_normal(ac, &_one, one).unwrap();
    let _one = crt.reduce(ac, one);
    equal_strict_in_field(ac, one, &_one).unwrap();

    {
        let a = &crt.assign_rand_in_rem(ac, rng);
        let a_red = &crt.reduce(ac, a);
        let x = &crt.assign_rand_in_rem(ac, rng);
        let neg_x = &crt.neg(ac, x);

        let c = &crt.mul(ac, a, zero, &[p, minus_one_neg, one], &[]);
        crt.assert_zero(ac, c).unwrap();
        equal_strict_in_field(ac, c, zero).unwrap();

        let c = &crt.mul(ac, a, p, &[x], &[x, p, minus_one_neg, one]);
        crt.assert_zero(ac, c).unwrap();
        equal_strict_in_field(ac, c, zero).unwrap();

        let c = &crt.mul(ac, a, neg_p, &[x, zero], &[x, p]);
        crt.assert_zero(ac, c).unwrap();
        equal_strict_in_field(ac, c, zero).unwrap();

        let c = &crt.mul(ac, a, one, &[x, neg_x], &[one, minus_one_neg]);
        equal_strict_in_field(ac, c, a_red).unwrap();

        let c = &crt.mul(ac, a, minus_one_neg, &[x, one, p], &[zero, x, one, neg_p]);
        let c = &c.add(ac, a);
        crt.assert_zero(ac, c).unwrap();
        equal_normal(ac, c, zero).unwrap();

        let c = &crt.mul(
            ac,
            minus_one_pos,
            minus_one_neg,
            &[one, p, neg_p],
            &[zero, one],
        );
        equal_strict_in_field(ac, c, one).unwrap();

        let c = &crt.mul(ac, minus_one_neg, one, &[], &[]);
        equal_normal(ac, c, minus_one_neg).unwrap();

        for _ in 0..10 {
            let a = &crt.assign_rand_in_rem_signed(ac, rng);
            let b_constant = rns.rand_in_rem(rng);
            let b = &crt
                .assign(ac, b_constant.uint().into(), &Range::Remainder)
                .unwrap();
            let to_add = (0..3)
                .map(|_| crt.assign_rand_in_max_signed(ac, rng))
                .collect_vec();
            let to_add = to_add.iter().collect_vec();
            let c0 = &crt.mul(ac, a, b, &to_add, &to_add);
            let c1 = crt.hint_mul(a, b, one, &to_add, &to_add);
            let c1 = &crt.assign(ac, c1.as_ref(), &Range::Remainder).unwrap();
            equal_strict_in_field(ac, c0, c1).unwrap();
            // let c2 = &crt.mul_constant(ac, a, &b_constant, &to_add, &to_add);
            // equal_strict_in_field(ac, c0, c2).unwrap();

            let c0 = &crt.square(ac, a, &to_add, &to_add);
            let c1 = crt.hint_mul(a, a, one, &to_add, &to_add);
            let c1 = &crt.assign(ac, c1.as_ref(), &Range::Remainder).unwrap();
            equal_strict_in_field(ac, c0, c1).unwrap();
        }
        {
            let a = &crt.assign_rand_in_op(ac, rng);
            let b = &crt.assign_rand_in_op(ac, rng);
            let neg_a = &crt.neg(ac, a);
            let c = &crt.div(ac, a, one);
            equal_normal(ac, c, a).unwrap();
            let c = &crt.div(ac, a, minus_one_neg);
            equal_normal(ac, c, neg_a).unwrap();
            let ab = &crt.div(ac, a, b);
            let c = &crt.mul(ac, ab, b, &[], &[]);
            equal_normal(ac, a, c).unwrap();
        }

        {
            let a = &crt.assign_rand_in_rem_signed(ac, rng);
            let x = &crt.assign_rand_in_rem_signed(ac, rng);
            let neg_a = &crt.neg(ac, a);
            let neg_x = &crt.neg(ac, x);

            let c = &crt.mul_div(ac, a, one, one, &[], &[]);
            equal_normal(ac, a, c).unwrap();
            let c = &crt.mul_div(ac, a, one, minus_one_neg, &[], &[]);
            equal_normal(ac, neg_a, c).unwrap();
            let c = &crt.mul_div(ac, a, one, a, &[], &[]);
            equal_normal(ac, one, c).unwrap();
            let c = &crt.mul_div(ac, a, a, a, &[], &[]);
            equal_normal(ac, a, c).unwrap();
            let c = &crt.mul_div(ac, a, a, neg_a, &[], &[]);
            equal_normal(ac, neg_a, c).unwrap();
            let c = &crt.mul_div(ac, a, neg_a, neg_a, &[], &[]);
            equal_normal(ac, a, c).unwrap();
            let c = &crt.mul_div(ac, a, x, neg_x, &[], &[]);
            equal_normal(ac, neg_a, c).unwrap();
            let c = &crt.mul_div(ac, zero, x, a, &[a], &[]);
            equal_normal(ac, one, c).unwrap();
        }

        for _ in 0..10 {
            let a = &crt.assign_rand_in_rem_signed(ac, rng);
            let b = &crt.assign_rand_in_rem_signed(ac, rng);
            let d = &crt.assign_rand_in_rem_signed(ac, rng);
            let to_add = (0..3)
                .map(|_| crt.assign_rand_in_max_signed(ac, rng))
                .collect_vec();
            let to_add = to_add.iter().collect_vec();
            let c0 = &crt.mul_div(ac, a, b, d, &to_add, &to_add);
            let c1 = crt.hint_mul(a, b, d, &to_add, &to_add);
            let c1 = &crt.assign(ac, c1.as_ref(), &Range::Remainder).unwrap();
            equal_normal(ac, c0, c1).unwrap();
        }
    }
}

#[allow(dead_code)]
fn run_var_crt_gadget_test<N: Field>() {
    use num_traits::Num;

    fn run<N: Field>(modulus: &str) {
        let mut rng = xor_rng();
        let mut ac = AbstractCircuit::<N>::default();
        ac.switch_sanity_check(true);
        let wrong_mod = BigUint::from_str_radix(modulus, 10).unwrap();
        let mod_size = wrong_mod.bits() as usize;
        let limb_size = 90;
        let sublimb_size = 15;
        var_crt_garget_test(
            &mut ac,
            &mut rng,
            (&wrong_mod).into(),
            mod_size,
            limb_size,
            sublimb_size,
        );
        // test_bug(&mut ac, &mut rng, &rns, sublimb_size);
    }

    // BN base field modulus
    run::<N>("21888242871839275222246405745257275088696311157297823662689037894645226208583");
    // BLS base field modulus
    run::<N>("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787");
    // BW6 base field modulus
    run::<N>("6891450384315732539396789682275657542479668912536150109513790160209623422243491736087683183289411687640864567753786613451161759120554247759349511699125301598951605099378508850372543631423596795951899700429969112842764913119068299");
    // 2048 RSA modulus
    run::<N>("25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357");
}

#[test]
#[cfg(any(feature = "arkworks", feature = "halo2"))]
fn test_var_crt_gadget() {
    #[cfg(feature = "arkworks")]
    use ark_bn254::Fr;
    #[cfg(feature = "halo2")]
    use halo2_proofs::halo2curves::bn256::Fr;
    run_var_crt_gadget_test::<Fr>()
}

#[test]
#[cfg(any(feature = "arkworks", feature = "halo2"))]
fn test_crt_gadget() {
    #[cfg(feature = "arkworks")]
    use ark_bn254::Fr;
    #[cfg(feature = "halo2")]
    use halo2_proofs::halo2curves::bn256::Fr;
    run_crt_gadget_test::<Fr>()
}
