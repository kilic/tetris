use super::{
    rns::{DivModResult, Range, Rns},
    VarBig,
};
use crate::{
    gadget::VarByte,
    ir::{
        ac::AbstractCircuit,
        combination::{quad::Qc, CombinationGadget},
    },
    qc, Error, Field, QuadScaled, Value, Var,
};
use itertools::{chain, izip, Itertools};
use num_bigint::{BigInt, BigUint, ToBigInt};
use num_integer::div_ceil;
use num_traits::One;
use num_traits::Zero;
use std::ops::Neg;

pub struct VarCrtGadget<N: Field> {
    pub(crate) rns: Rns<N>,
    pub(crate) wrong_mod: VarBig<N>,
}

impl<N: Field> VarCrtGadget<N> {
    pub fn new(
        ac: &mut AbstractCircuit<N>,
        mod_size: usize,
        limb_size: usize,
        sublimb_size: usize,
        wrong_mod: Value<&BigUint>,
    ) -> Result<Self, Error> {
        let rns = Rns::construct(mod_size, limb_size, sublimb_size);
        wrong_mod.maybe(|wrong_mod| {
            ac.sanity_some(|| (wrong_mod.bits() as usize <= mod_size).then_some(()))
        })?;
        let wrong_mod = rns.assign(ac, wrong_mod, &Range::Remainder)?;
        Ok(Self { rns, wrong_mod })
    }

    pub fn rns(&self) -> &Rns<N> {
        &self.rns
    }

    pub fn wrong_mod(&self) -> &VarBig<N> {
        &self.wrong_mod
    }

    pub fn to_bytes(&self, ac: &mut AbstractCircuit<N>, w: &VarBig<N>) -> Vec<VarByte<N>> {
        self.rns.into_bytes(ac, w)
    }

    pub(crate) fn witgen_red(&self, w: Value<&BigInt>) -> DivModResult {
        let wrong_mod = self.wrong_mod.int();
        self.rns.witgen_red(w, wrong_mod)
    }

    pub(crate) fn witgen_mul(
        &self,
        w0: Value<&BigInt>,
        w1: Value<&BigInt>,
        d: Value<&BigInt>,
        to_add: &[Value<BigInt>],
    ) -> DivModResult {
        let wrong_mod = self.wrong_mod.int();
        self.rns.witgen_mul(w0, w1, d, to_add, wrong_mod)
    }

    pub(crate) fn reduce_operand(&self, ac: &mut AbstractCircuit<N>, e: &VarBig<N>) -> VarBig<N> {
        if e.max().unwrap() > &self.rns.max_op {
            ac.log_incr("big-field-forced-red");
            self.reduce(ac, e)
        } else {
            e.clone()
        }
    }

    pub fn assign(
        &self,
        ac: &mut AbstractCircuit<N>,
        value: Value<&BigUint>,
        range: &Range,
    ) -> Result<VarBig<N>, Error> {
        self.rns.assign(ac, value, range)
    }

    pub fn assign_signed(
        &self,
        ac: &mut AbstractCircuit<N>,
        value: Value<&BigInt>,
        range: &Range,
    ) -> Result<VarBig<N>, Error> {
        self.rns.assign_signed(ac, value, range)
    }

    pub fn get_constant(
        &self,
        ac: &mut AbstractCircuit<N>,
        constant: &BigUint,
    ) -> Result<VarBig<N>, Error> {
        self.rns.get_constant(ac, constant)
    }

    fn assign_mul_witness(
        &self,
        ac: &mut AbstractCircuit<N>,
        w0: Value<&BigInt>,
        w1: Option<Value<&BigInt>>,
        d: Option<Value<&BigInt>>,
        to_add: &[Value<&BigInt>],
        to_sub: &[Value<&BigInt>],
    ) -> (VarBig<N>, VarBig<N>) {
        let one: Value<_> = BigInt::one().into();
        let witness = {
            let to_add = to_add.iter().map(|e| e.cloned());
            let to_sub = to_sub.iter().map(|e| e.neg());
            self.witgen_mul(
                w0,
                w1.unwrap_or(one.as_ref()),
                d.unwrap_or(one.as_ref()),
                &chain!(to_add, to_sub).collect_vec(),
            )
        };
        let quot = self
            .rns
            .assign_signed(ac, witness.q(), &Range::Quotient)
            .unwrap();
        let res = self.rns.assign(ac, witness.r(), &Range::Remainder).unwrap();
        (quot, res)
    }

    pub fn reduce(&self, ac: &mut AbstractCircuit<N>, w: &VarBig<N>) -> VarBig<N> {
        ac.log_incr("var-big-field-red");
        let witness = self.witgen_red(w.int());
        let res = self.rns.assign(ac, witness.r(), &Range::Remainder).unwrap();
        let quot_size = w
            .max()
            .unwrap()
            .bits()
            .saturating_sub(self.rns.max_rem.bits())
            + 1;
        let quot = witness.q().map(|q| {
            ac.log_max("var-big-field-q-max", q.bits());
            N::from_int(q).unwrap()
        });
        let quot = ac
            .decompose_assign_signed(self.rns.sublimb_size, quot_size as usize, &quot)
            .unwrap();

        let max_carries = self.rns.red_max_carries(&w.max_limbs());
        let mut carry: Option<Var<N>> = None;
        w.limbs_var()
            .zip(res.limbs_var())
            .zip(self.wrong_mod.limbs_var())
            .zip(max_carries)
            .for_each(|(((limb, res), p), max_carry)| {
                let mut qc = qc!();
                qc += limb;
                qc -= quot * p;
                qc -= res;
                self.rns.update_carry_qc(ac, &mut carry, max_carry, qc);
            });

        let mut qc = qc!();
        qc += w.nat();
        qc -= quot * self.wrong_mod.nat();
        qc -= res.nat();
        ac.zero_sum(qc).unwrap();
        res
    }

    pub fn assert_zero(&self, ac: &mut AbstractCircuit<N>, w: &VarBig<N>) -> Result<(), Error> {
        let witness = self.witgen_red(w.int());
        ac.sanity_ok(|| witness.r.maybe(|e| e.is_zero().then_some(())))?;
        let quot_size = w
            .max()
            .unwrap()
            .bits()
            .saturating_sub(self.rns.max_rem.bits())
            + 1;
        let quot = witness.q().map(|q| N::from_int(q).unwrap());
        let quot = ac
            .decompose_assign_signed(self.rns.sublimb_size, quot_size as usize, &quot)
            .unwrap();

        let max_carries = self.rns.red_max_carries(&w.max_limbs());
        let mut carry: Option<Var<N>> = None;
        w.limbs_var()
            .zip(self.wrong_mod.limbs_var())
            .zip(max_carries)
            .for_each(|((limb, p), max_carry)| {
                let mut qc = qc!();
                qc += limb;
                qc -= quot * p;
                self.rns.update_carry_qc(ac, &mut carry, max_carry, qc);
            });

        let mut qc = qc!();
        qc += w.nat();
        qc -= quot * self.wrong_mod.nat();
        ac.zero_sum(qc)?;

        Ok(())
    }

    pub fn normal_equal(
        &self,
        ac: &mut AbstractCircuit<N>,
        w0: &VarBig<N>,
        w1: &VarBig<N>,
    ) -> Result<(), Error> {
        let dif = w0.sub(ac, w1);
        self.assert_zero(ac, &dif)
    }

    pub fn mul(
        &self,
        ac: &mut AbstractCircuit<N>,
        w0: &VarBig<N>,
        w1: &VarBig<N>,
        to_add: &[&VarBig<N>],
        to_sub: &[&VarBig<N>],
    ) -> VarBig<N> {
        let w0 = &self.reduce_operand(ac, w0);
        let w1 = &self.reduce_operand(ac, w1);
        let to_add = to_add.iter().cloned().cloned().collect_vec();
        let mut to_sub = to_sub.iter().cloned().cloned().collect_vec();
        let (quot, res) = self.assign_mul_witness(
            ac,
            w0.int(),
            Some(w1.int()),
            None,
            &to_add.iter().map(VarBig::int).collect_vec(),
            &to_sub.iter().map(VarBig::int).collect_vec(),
        );

        // find max carries
        let max_carries = {
            let to_add = to_add.iter().map(VarBig::max_limbs).collect_vec();
            let to_sub = to_sub.iter().map(VarBig::max_limbs).collect_vec();
            self.rns.mul_max_carries(
                &w0.max_limbs(),
                &w1.max_limbs(),
                None,
                &chain(to_add, to_sub).collect_vec(),
            )
        };

        // mul into combination terms
        let mut quad = w0.product(w1);
        quad.iter_mut()
            .zip(quot.product(&self.wrong_mod))
            .for_each(|(a, mut b)| {
                b.iter_mut().for_each(QuadScaled::neg_assign);
                a.extend(b);
            });

        // result is degree 1 term
        to_sub.push(res.clone());
        let mut lin = vec![vec![]; self.rns.n_limbs()];

        // transpose-collect limbs of degree 1 terms
        to_add.iter().for_each(|e| {
            izip!(e.limbs_var(), lin.iter_mut()).for_each(|(e, lin)| lin.push(e.into()))
        });
        to_sub.iter().for_each(|e| {
            izip!(e.limbs_var(), lin.iter_mut()).for_each(|(e, lin)| lin.push(e.neg()))
        });

        // eval carries of partial schoolbook multiplication
        self.rns.eval_quad(ac, &quad, &lin, max_carries);

        // constrain in native field
        let mut qc = qc!();
        qc += w0.nat() * w1.nat();
        qc += to_add.iter().map(VarBig::nat);
        qc -= to_sub.iter().map(VarBig::nat);
        qc -= quot.nat() * self.wrong_mod.nat();
        ac.zero_sum(qc).unwrap();

        res
    }

    pub fn square(
        &self,
        ac: &mut AbstractCircuit<N>,
        w0: &VarBig<N>,
        to_add: &[&VarBig<N>],
        to_sub: &[&VarBig<N>],
    ) -> VarBig<N> {
        let w0 = &self.reduce_operand(ac, w0);
        let to_add: Vec<VarBig<N>> = to_add.iter().cloned().cloned().collect_vec();
        let mut to_sub = to_sub.iter().cloned().cloned().collect_vec();
        let (quot, res) = self.assign_mul_witness(
            ac,
            w0.int(),
            Some(w0.int()),
            None,
            &to_add.iter().map(VarBig::int).collect_vec(),
            &to_sub.iter().map(VarBig::int).collect_vec(),
        );

        // find max carries
        let max_carries = {
            let to_add = to_add.iter().map(VarBig::max_limbs).collect_vec();
            let to_sub = to_sub.iter().map(VarBig::max_limbs).collect_vec();
            let w0 = w0.max_limbs();
            self.rns
                .mul_max_carries(&w0, &w0, None, &chain(to_add, to_sub).collect_vec())
        };

        // t0 = a0a0
        // t1 = 2 * a0a1
        // t2 = 2 * a0a2 + a1a1
        // t3 = 2 * a0a3 + 2 * a1a2
        // t4 = 2 * a0a4 + 2 * a1a3 + a2a2

        // convert into cobination terms
        let quad = w0.product(w0);
        let mut quad = quad
            .iter()
            .map(|t| {
                let off = div_ceil(t.len(), 2);
                t.iter()
                    .take(off)
                    .enumerate()
                    .map(|(i, e)| {
                        e * if t.len() & 1 == 1 && i == off - 1 {
                            N::from_u64(1)
                        } else {
                            N::from_u64(2)
                        }
                    })
                    .collect_vec()
            })
            .collect_vec();
        quad.iter_mut()
            .zip(quot.product(&self.wrong_mod))
            .for_each(|(a, mut b)| {
                b.iter_mut().for_each(QuadScaled::neg_assign);
                a.extend(b);
            });

        // result is degree 1 term
        to_sub.push(res.clone());
        let mut lin = vec![vec![]; self.rns.n_limbs()];

        // transpose-collect limbs of degree 1 terms
        to_add.iter().for_each(|e| {
            izip!(e.limbs_var(), lin.iter_mut()).for_each(|(e, lin)| lin.push(e.into()))
        });
        to_sub.iter().for_each(|e| {
            izip!(e.limbs_var(), lin.iter_mut()).for_each(|(e, lin)| lin.push(e.neg()))
        });

        // eval carries of partial schoolbook multiplication
        self.rns.eval_quad(ac, &quad, &lin, max_carries);

        // constrain in native field
        let mut qc = qc!();
        qc += w0.nat() * w0.nat();
        qc += to_add.iter().map(VarBig::nat);
        qc -= to_sub.iter().map(VarBig::nat);
        qc -= quot.nat() * self.wrong_mod.nat();
        ac.zero_sum(qc).unwrap();

        res
    }

    pub fn div(&self, ac: &mut AbstractCircuit<N>, w0: &VarBig<N>, w1: &VarBig<N>) -> VarBig<N> {
        let w1 = &self.reduce_operand(ac, w1);
        let (quot, res) = self.assign_mul_witness(ac, w0.int(), None, Some(w1.int()), &[], &[]);

        let max_carries =
            self.rns
                .mul_max_carries(&w1.max_limbs(), &res.max_limbs(), None, &[w0.max_limbs()]);

        // mul into combination terms
        let mut quad = w1.product(&res);
        quad.iter_mut()
            .zip(quot.product(&self.wrong_mod))
            .for_each(|(a, b)| a.extend(b));
        let mut lin = vec![vec![]; self.rns.n_limbs()];
        izip!(w0.limbs_var(), lin.iter_mut()).for_each(|(e, lin)| lin.push(e.neg()));
        self.rns.eval_quad(ac, &quad, &lin, max_carries);

        let mut qc = qc!();
        qc += w1.nat() * res.nat();
        qc -= w0.nat();
        qc += quot.nat() * self.wrong_mod.nat();
        ac.zero_sum(qc).unwrap();

        res
    }

    pub fn mul_div(
        &self,
        ac: &mut AbstractCircuit<N>,
        w0: &VarBig<N>,
        w1: &VarBig<N>,
        d: &VarBig<N>,
        to_add: &[&VarBig<N>],
        to_sub: &[&VarBig<N>],
    ) -> VarBig<N> {
        let w0 = &self.reduce_operand(ac, w0);
        let w1 = &self.reduce_operand(ac, w1);
        let d = &self.reduce_operand(ac, d);
        let to_add = to_add.iter().cloned().cloned().collect_vec();
        let to_sub = to_sub.iter().cloned().cloned().collect_vec();
        let (quot, res) = self.assign_mul_witness(
            ac,
            w0.int(),
            Some(w1.int()),
            Some(d.int()),
            &to_add.iter().map(VarBig::int).collect_vec(),
            &to_sub.iter().map(VarBig::int).collect_vec(),
        );

        // find max carries
        let max_carries = {
            let to_add = to_add.iter().map(VarBig::max_limbs).collect_vec();
            let to_sub = to_sub.iter().map(VarBig::max_limbs).collect_vec();
            self.rns.mul_max_carries(
                &w0.max_limbs(),
                &w1.max_limbs(),
                Some(&d.max_limbs()),
                &chain(to_add, to_sub).collect_vec(),
            )
        };

        // mul into combination terms
        let mut quad = w0.product(w1);
        quad.iter_mut().zip(res.product(d)).for_each(|(a, mut b)| {
            b.iter_mut().for_each(QuadScaled::neg_assign);
            a.extend(b);
        });

        quad.iter_mut()
            .zip(quot.product(&self.wrong_mod))
            .for_each(|(a, mut b)| {
                b.iter_mut().for_each(QuadScaled::neg_assign);
                a.extend(b);
            });

        let mut lin = vec![vec![]; self.rns.n_limbs()];

        // transpose-collect limbs of degree 0 terms
        to_add.iter().for_each(|e| {
            izip!(e.limbs_var(), lin.iter_mut()).for_each(|(e, lin)| lin.push(e.into()))
        });
        to_sub.iter().for_each(|e| {
            izip!(e.limbs_var(), lin.iter_mut()).for_each(|(e, lin)| lin.push(e.neg()))
        });

        // eval carries of partial schoolbook multiplication
        self.rns.eval_quad(ac, &quad, &lin, max_carries);

        let mut qc = qc!();
        qc += w0.nat() * w1.nat();
        qc -= res.nat() * d.nat();
        qc += to_add.iter().map(VarBig::nat);
        qc -= to_sub.iter().map(VarBig::nat);
        qc -= quot.nat() * self.wrong_mod.nat();
        ac.zero_sum(qc).unwrap();

        res
    }

    pub fn assert_in_field(
        &self,
        ac: &mut AbstractCircuit<N>,
        w0: &VarBig<N>,
    ) -> Result<(), Error> {
        let w0 = self.reduce(ac, w0);
        // TODO: fix this
        let minus_one = self.wrong_mod();

        let mut borrows = vec![];
        let mut prev_borrow = BigUint::zero();
        let limb_size = self.rns.limb_size;
        let result: Vec<_> = izip!(w0.limbs(), minus_one.limbs())
            .enumerate()
            .map(|(i, (w0, w1))| {
                let is_last = i == (self.rns.n_limbs - 1);
                let w0 = w0.uint();
                let w1 = w1.uint();
                let (limb, borrow) = w0
                    .zip(w1)
                    .map(|(w0, w1)| {
                        let cur_borrow: BigUint =
                            (if w1 < &(w0 + &prev_borrow) { 1usize } else { 0 }).into();
                        let limb = ((w1 + (&cur_borrow << limb_size)) - &prev_borrow) - w0;
                        prev_borrow = cur_borrow;
                        (
                            limb.to_bigint().unwrap(),
                            N::from_uint(&prev_borrow).unwrap(),
                        )
                    })
                    .unzip();
                if !is_last {
                    borrows.push(ac.assign_bit(&borrow)?);
                }
                Ok(limb)
            })
            .try_collect()?;

        let result = self
            .rns
            .assign_limbs(ac, false, &result, &Range::Remainder)?;

        let mut qc = qc!();
        qc += minus_one.limb_at(0);
        qc -= w0.limb_at(0);
        qc -= result[0].var();
        qc += borrows[0] * self.rns.lsh();
        ac.zero_sum(qc)?;

        for i in 1..self.rns.n_limbs - 1 {
            let mut qc = qc!();
            qc += minus_one.limb_at(i);
            qc -= w0.limb_at(i);
            qc -= result[i].var();
            qc += borrows[i] * self.rns.lsh();
            qc -= borrows[i - 1];
            ac.zero_sum(qc)?
        }

        let i = self.rns.n_limbs - 1;
        let mut qc = qc!();
        qc += minus_one.limb_at(i);
        qc -= w0.limb_at(i);
        qc -= result[i].var();
        qc -= borrows[i - 1];
        ac.zero_sum(qc)?;

        Ok(())
    }

    pub fn neg(&self, ac: &mut AbstractCircuit<N>, w: &VarBig<N>) -> VarBig<N> {
        self.wrong_mod.sub(ac, w)
    }

    pub fn is_zero(&self, ac: &mut AbstractCircuit<N>, w: &VarBig<N>) -> Var<N> {
        let w = self.reduce(ac, w);
        self.assert_in_field(ac, &w).unwrap();
        w.limbs()
            .fold(None, |acc, limb| {
                let is_zero = ac.is_zero(limb.var());
                acc.map(|acc| ac.and(&is_zero, &acc)).or(Some(is_zero))
            })
            .unwrap()
    }

    pub fn is_one(&self, ac: &mut AbstractCircuit<N>, w: &VarBig<N>) -> Var<N> {
        let w = self.reduce(ac, w);
        self.assert_in_field(ac, &w).unwrap();
        let acc = ac.is_one(w.limb_at(0));
        w.limbs().skip(1).fold(acc, |acc, limb| {
            let is_zero = ac.is_zero(limb.var());
            ac.mul(&is_zero, &acc)
        })
    }

    pub fn assert_not_zero(&self, ac: &mut AbstractCircuit<N>, w: &VarBig<N>) -> Result<(), Error> {
        let is_zero = self.is_zero(ac, w);
        ac.assert_zero(&is_zero)
    }

    pub fn is_equal(&self, ac: &mut AbstractCircuit<N>, w0: &VarBig<N>, w1: &VarBig<N>) -> Var<N> {
        let dif = w0.sub(ac, w1);
        self.is_zero(ac, &dif)
    }

    pub fn assert_not_equal(
        &self,
        ac: &mut AbstractCircuit<N>,
        w0: &VarBig<N>,
        w1: &VarBig<N>,
    ) -> Result<(), Error> {
        let dif = w0.sub(ac, w1);
        self.assert_not_zero(ac, &dif)
    }
}
