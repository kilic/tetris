use super::{witness::BNPairing, BNPairingGadget};
use crate::{
    gadget::big_field::{Big, VarBig},
    ir::ac::AbstractCircuit,
    Error, Field, Value, Var,
};
use itertools::Itertools;
use num_bigint::BigUint;
use num_traits::One;
use num_traits::Zero;

#[derive(Clone, Debug)]
pub struct E2<N> {
    pub(crate) e0: N,
    pub(crate) e1: N,
}

impl<N> E2<N> {
    pub(crate) fn new(e0: N, e1: N) -> Self {
        Self { e0, e1 }
    }
}

impl<N: Field> E2<VarBig<N>> {
    pub(crate) fn value(&self) -> Value<E2<BigUint>> {
        self.e0.uint().zip(self.e1.uint()).map(|(e0, e1)| E2 {
            e0: e0.clone(),
            e1: e1.clone(),
        })
    }
}

impl<N: Field, BNPairingEngine: BNPairing> BNPairingGadget<N, BNPairingEngine> {
    pub fn e2_assign(
        &self,
        ac: &mut AbstractCircuit<N>,
        e: Value<E2<BigUint>>,
    ) -> Result<E2<VarBig<N>>, Error> {
        let e0 = self.assign_base_field(ac, e.as_ref().map(|e| &e.e0))?;
        let e1 = self.assign_base_field(ac, e.as_ref().map(|e| &e.e1))?;
        Ok(E2 { e0, e1 })
    }

    pub(crate) fn e2_add(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
        b: &E2<VarBig<N>>,
    ) -> E2<VarBig<N>> {
        E2 {
            e0: a.e0.add(ac, &b.e0),
            e1: a.e1.add(ac, &b.e1),
        }
    }

    pub(crate) fn e2_add_constant(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
        b: &E2<Big<N>>,
    ) -> E2<VarBig<N>> {
        E2 {
            e0: a.e0.add_constant(ac, &b.e0),
            e1: a.e1.add_constant(ac, &b.e1),
        }
    }

    pub(crate) fn e2_normal_equal(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
        b: &E2<VarBig<N>>,
    ) -> Result<(), Error> {
        self.base_field.normal_equal(ac, &a.e0, &b.e0)?;
        self.base_field.normal_equal(ac, &a.e1, &b.e1)?;
        Ok(())
    }

    pub(crate) fn e2_assert_zero(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
    ) -> Result<(), Error> {
        self.base_field.assert_zero(ac, &a.e0)?;
        self.base_field.assert_zero(ac, &a.e1)?;
        Ok(())
    }

    pub(crate) fn e2_select(
        &self,
        ac: &mut AbstractCircuit<N>,
        cond: &Var<N>,
        e0: &E2<VarBig<N>>,
        e1: &E2<VarBig<N>>,
    ) -> Result<E2<VarBig<N>>, Error> {
        let t0 = e0.e0.select(ac, cond, &e1.e0)?;
        let t1 = e0.e1.select(ac, cond, &e1.e1)?;
        Ok(E2 { e0: t0, e1: t1 })
    }

    pub(crate) fn e2_reduce(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
    ) -> E2<VarBig<N>> {
        E2 {
            e0: self.base_field.reduce(ac, &a.e0),
            e1: self.base_field.reduce(ac, &a.e1),
        }
    }

    pub(crate) fn e2_constant(
        &self,
        ac: &mut AbstractCircuit<N>,
        constant: &E2<BigUint>,
    ) -> Result<E2<VarBig<N>>, Error> {
        let e0 = self.base_field.get_constant(ac, &constant.e0)?;
        let e1 = self.base_field.get_constant(ac, &constant.e1)?;
        Ok(E2 { e0, e1 })
    }

    pub(crate) fn e2_one(&self, ac: &mut AbstractCircuit<N>) -> E2<VarBig<N>> {
        let one = self.base_field.get_constant(ac, &BigUint::one()).unwrap();
        let zero = self.base_field.get_constant(ac, &BigUint::zero()).unwrap();
        E2 { e0: one, e1: zero }
    }

    pub(crate) fn e2_zero(&self, ac: &mut AbstractCircuit<N>) -> E2<VarBig<N>> {
        let zero = self.base_field.get_constant(ac, &BigUint::zero()).unwrap();
        E2 {
            e0: zero.clone(),
            e1: zero,
        }
    }

    pub(crate) fn e2_double(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
    ) -> E2<VarBig<N>> {
        E2 {
            e0: a.e0.double(ac),
            e1: a.e1.double(ac),
        }
    }

    pub(crate) fn e2_triple(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
    ) -> E2<VarBig<N>> {
        E2 {
            e0: a.e0.triple(ac),
            e1: a.e1.triple(ac),
        }
    }

    pub(crate) fn e2_sub(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
        b: &E2<VarBig<N>>,
    ) -> E2<VarBig<N>> {
        E2 {
            e0: a.e0.sub(ac, &b.e0),
            e1: a.e1.sub(ac, &b.e1),
        }
    }

    pub(crate) fn e2_neg(&self, ac: &mut AbstractCircuit<N>, a: &E2<VarBig<N>>) -> E2<VarBig<N>> {
        E2 {
            e0: self.base_field.neg(ac, &a.e0),
            e1: self.base_field.neg(ac, &a.e1),
        }
    }

    pub(crate) fn e2_conj(&self, ac: &mut AbstractCircuit<N>, a: &E2<VarBig<N>>) -> E2<VarBig<N>> {
        E2 {
            e0: a.e0.clone(),
            e1: self.base_field.neg(ac, &a.e1),
        }
    }

    pub(crate) fn e2_mul(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
        b: &E2<VarBig<N>>,
    ) -> E2<VarBig<N>> {
        let m0 = self.base_field.mul(ac, &a.e0, &b.e0, &[], &[]);
        let m1 = self.base_field.mul(ac, &a.e1, &b.e1, &[], &[]);
        let e0 = m0.sub(ac, &m1);
        let a01 = a.e0.add(ac, &a.e1);
        let b01 = b.e0.add(ac, &b.e1);
        let e1 = self.base_field.mul(ac, &a01, &b01, &[], &[&m0, &m1]);
        E2 { e0, e1 }
    }

    pub(crate) fn e2_mul_sub(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
        b: &E2<VarBig<N>>,
        to_sub: &E2<VarBig<N>>,
    ) -> E2<VarBig<N>> {
        let m0 = self.base_field.mul(ac, &a.e0, &b.e0, &[], &[]);
        let m1 = self.base_field.mul(ac, &a.e1, &b.e1, &[], &[]);
        let e0 = m0.sub(ac, &m1);
        let e0 = e0.sub(ac, &to_sub.e0);
        let a01 = a.e0.add(ac, &a.e1);
        let b01 = b.e0.add(ac, &b.e1);
        let e1 = self
            .base_field
            .mul(ac, &a01, &b01, &[], &[&m0, &m1, &to_sub.e1]);
        E2 { e0, e1 }
    }

    pub(crate) fn e2_mul_by_e(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
        b: &VarBig<N>,
    ) -> E2<VarBig<N>> {
        E2 {
            e0: self.base_field.mul(ac, &a.e0, b, &[], &[]),
            e1: self.base_field.mul(ac, &a.e1, b, &[], &[]),
        }
    }

    pub(crate) fn e2_mul_by_constant_e(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<Big<N>>,
        b: &VarBig<N>,
    ) -> E2<VarBig<N>> {
        E2 {
            e0: self.base_field.mul_constant(ac, b, &a.e0, &[], &[]),
            e1: self.base_field.mul_constant(ac, b, &a.e1, &[], &[]),
        }
    }

    pub(crate) fn e2_inv(&self, ac: &mut AbstractCircuit<N>, a: &E2<VarBig<N>>) -> E2<VarBig<N>> {
        let t = &self.base_field.square(ac, &a.e0, &[], &[]);
        let t = self.base_field.square(ac, &a.e1, &[t], &[]);
        let e0 = self.base_field.div(ac, &a.e0, &t);
        let e1 = self.base_field.div(ac, &a.e1, &t);
        let e1 = self.base_field.neg(ac, &e1);
        E2 { e0, e1 }
    }

    pub(crate) fn e2_mul_constant(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
        b: &E2<Big<N>>,
    ) -> E2<VarBig<N>> {
        let t1 = self.base_field.mul_constant(ac, &a.e0, &b.e0, &[], &[]);
        let t2 = self.base_field.mul_constant(ac, &a.e1, &b.e1, &[], &[]);
        let t0 = a.e0.add(ac, &a.e1);
        let t3 = b.e0.uint() + b.e1.uint();
        let t3 = self.base_field.rns().big_from_uint(&t3);
        let e0 = t1.sub(ac, &t2);
        let e1 = self.base_field.mul_constant(ac, &t0, &t3, &[], &[&t1, &t2]);
        E2 { e0, e1 }
    }

    pub(crate) fn e2_square(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
    ) -> E2<VarBig<N>> {
        let t0 = a.e0.add(ac, &a.e1);
        let t1 = a.e0.sub(ac, &a.e1);
        let t2 = a.e0.double(ac);
        let e0 = self.base_field.mul(ac, &t0, &t1, &[], &[]);
        let e1 = self.base_field.mul(ac, &t2, &a.e1, &[], &[]);
        E2 { e0, e1 }
    }

    pub(crate) fn e2_square_sub(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
        to_sub: &[&E2<VarBig<N>>],
    ) -> E2<VarBig<N>> {
        let t0 = a.e0.add(ac, &a.e1);
        let t1 = a.e0.sub(ac, &a.e1);
        let t2 = a.e0.double(ac);

        let to_sub0 = to_sub.iter().map(|e| &e.e0).collect_vec();
        let e0 = self.base_field.mul(ac, &t0, &t1, &[], &to_sub0);

        let to_sub1 = to_sub.iter().map(|e| &e.e1).collect_vec();
        let e1 = self.base_field.mul(ac, &t2, &a.e1, &[], &to_sub1);
        E2 { e0, e1 }
    }

    pub(crate) fn e2_mul_by_non_residue(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
    ) -> E2<VarBig<N>> {
        let t0 = &a.e1.mul_small(ac, 8);
        let t0 = t0.add(ac, &a.e1);
        let t0 = t0.add(ac, &a.e0);
        let t1 = &a.e0.mul_small(ac, 8);
        let t1 = t1.add(ac, &a.e0);
        let t1 = t1.sub(ac, &a.e1);

        E2 { e0: t1, e1: t0 }
    }

    pub(crate) fn e2_frobenius_map(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E2<VarBig<N>>,
        power: usize,
    ) -> E2<VarBig<N>> {
        if power % 2 != 0 {
            self.e2_conj(ac, a)
        } else {
            a.clone()
        }
    }
}
