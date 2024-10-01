use super::{e2::E2, witness::BNPairing, BNPairingGadget};
use crate::{gadget::big_field::VarBig, ir::ac::AbstractCircuit, Error, Field, Value, Var};
use num_bigint::BigUint;

#[derive(Clone, Debug)]
pub(crate) struct E6<N> {
    pub(crate) e0: E2<N>,
    pub(crate) e1: E2<N>,
    pub(crate) e2: E2<N>,
}

impl<N> E6<N> {
    pub(crate) fn new(e0: E2<N>, e1: E2<N>, e2: E2<N>) -> Self {
        Self { e0, e1, e2 }
    }
}

impl<N: Field> E6<VarBig<N>> {
    pub(crate) fn value(&self) -> Value<E6<BigUint>> {
        self.e0
            .value()
            .zip(self.e1.value())
            .zip(self.e2.value())
            .map(|((e0, e1), e2)| E6 { e0, e1, e2 })
    }
}

impl<N: Field, BNPairingEngine: BNPairing> BNPairingGadget<N, BNPairingEngine> {
    pub(crate) fn e6_one(&self, ac: &mut AbstractCircuit<N>) -> E6<VarBig<N>> {
        E6 {
            e0: self.e2_one(ac),
            e1: self.e2_zero(ac),
            e2: self.e2_zero(ac),
        }
    }

    pub(crate) fn e6_zero(&self, ac: &mut AbstractCircuit<N>) -> E6<VarBig<N>> {
        E6 {
            e0: self.e2_zero(ac),
            e1: self.e2_zero(ac),
            e2: self.e2_zero(ac),
        }
    }

    pub(crate) fn e6_reduce(
        &self,
        ac: &mut AbstractCircuit<N>,
        e: &E6<VarBig<N>>,
    ) -> E6<VarBig<N>> {
        E6 {
            e0: self.e2_reduce(ac, &e.e0),
            e1: self.e2_reduce(ac, &e.e1),
            e2: self.e2_reduce(ac, &e.e2),
        }
    }

    pub(crate) fn e6_assign(
        &self,
        ac: &mut AbstractCircuit<N>,
        e: Value<E6<BigUint>>,
    ) -> Result<E6<VarBig<N>>, Error> {
        Ok(E6 {
            e0: self.e2_assign(ac, e.as_ref().map(|e| e.e0.clone()))?,
            e1: self.e2_assign(ac, e.as_ref().map(|e| e.e1.clone()))?,
            e2: self.e2_assign(ac, e.as_ref().map(|e| e.e2.clone()))?,
        })
    }

    pub(crate) fn e6_constant(
        &self,
        ac: &mut AbstractCircuit<N>,
        e: E6<BigUint>,
    ) -> Result<E6<VarBig<N>>, Error> {
        Ok(E6 {
            e0: self.e2_constant(ac, &e.e0)?,
            e1: self.e2_constant(ac, &e.e1)?,
            e2: self.e2_constant(ac, &e.e2)?,
        })
    }

    pub(crate) fn e6_select(
        &self,
        ac: &mut AbstractCircuit<N>,
        cond: &Var<N>,
        e0: &E6<VarBig<N>>,
        e1: &E6<VarBig<N>>,
    ) -> Result<E6<VarBig<N>>, Error> {
        Ok(E6 {
            e0: self.e2_select(ac, cond, &e0.e0, &e1.e0)?,
            e1: self.e2_select(ac, cond, &e0.e1, &e1.e1)?,
            e2: self.e2_select(ac, cond, &e0.e2, &e1.e2)?,
        })
    }

    pub(crate) fn e6_assert_zero(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E6<VarBig<N>>,
    ) -> Result<(), Error> {
        self.e2_assert_zero(ac, &a.e0)?;
        self.e2_assert_zero(ac, &a.e1)?;
        self.e2_assert_zero(ac, &a.e2)?;
        Ok(())
    }

    pub(crate) fn e6_add(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E6<VarBig<N>>,
        b: &E6<VarBig<N>>,
    ) -> E6<VarBig<N>> {
        let e0 = self.e2_add(ac, &a.e0, &b.e0);
        let e1 = self.e2_add(ac, &a.e1, &b.e1);
        let e2 = self.e2_add(ac, &a.e2, &b.e2);
        E6 { e0, e1, e2 }
    }

    pub(crate) fn e6_double(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E6<VarBig<N>>,
    ) -> E6<VarBig<N>> {
        let e0 = self.e2_double(ac, &a.e0);
        let e1 = self.e2_double(ac, &a.e1);
        let e2 = self.e2_double(ac, &a.e2);
        E6 { e0, e1, e2 }
    }

    pub(crate) fn e6_sub(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E6<VarBig<N>>,
        b: &E6<VarBig<N>>,
    ) -> E6<VarBig<N>> {
        let e0 = self.e2_sub(ac, &a.e0, &b.e0);
        let e1 = self.e2_sub(ac, &a.e1, &b.e1);
        let e2 = self.e2_sub(ac, &a.e2, &b.e2);
        E6 { e0, e1, e2 }
    }

    pub(crate) fn e6_neg(&self, ac: &mut AbstractCircuit<N>, a: &E6<VarBig<N>>) -> E6<VarBig<N>> {
        let e0 = self.e2_neg(ac, &a.e0);
        let e1 = self.e2_neg(ac, &a.e1);
        let e2 = self.e2_neg(ac, &a.e2);
        E6 { e0, e1, e2 }
    }

    pub(crate) fn e6_mul(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E6<VarBig<N>>,
        b: &E6<VarBig<N>>,
    ) -> E6<VarBig<N>> {
        let t0 = self.e2_mul(ac, &a.e0, &b.e0);
        let t1 = self.e2_mul(ac, &a.e1, &b.e1);
        let t2 = self.e2_mul(ac, &a.e2, &b.e2);
        let t3 = self.e2_add(ac, &a.e1, &a.e2);
        let t4 = self.e2_add(ac, &b.e1, &b.e2);
        let t3 = self.e2_mul(ac, &t3, &t4);
        let t4 = self.e2_add(ac, &t1, &t2);
        let t3 = self.e2_sub(ac, &t3, &t4);
        let t3 = self.e2_mul_by_non_residue(ac, &t3);
        let t5 = self.e2_add(ac, &t0, &t3);
        let t3 = self.e2_add(ac, &a.e0, &a.e1);
        let t4 = self.e2_add(ac, &b.e0, &b.e1);
        let t3 = self.e2_mul(ac, &t3, &t4);
        let t4 = self.e2_add(ac, &t0, &t1);
        let t3 = self.e2_sub(ac, &t3, &t4);
        let t4 = self.e2_mul_by_non_residue(ac, &t2);
        let e1 = self.e2_add(ac, &t3, &t4);
        let t3 = self.e2_add(ac, &a.e0, &a.e2);
        let t4 = self.e2_add(ac, &b.e0, &b.e2);
        let t3 = self.e2_mul(ac, &t3, &t4);
        let t4 = self.e2_add(ac, &t0, &t2);
        let t3 = self.e2_sub(ac, &t3, &t4);
        let e2 = self.e2_add(ac, &t1, &t3);
        let e0 = t5;

        E6 { e0, e1, e2 }
    }

    pub(crate) fn e6_mul_by_01(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E6<VarBig<N>>,
        e0: &E2<VarBig<N>>,
        e1: &E2<VarBig<N>>,
    ) -> E6<VarBig<N>> {
        let a_a = self.e2_mul(ac, &a.e0, e0);
        let b_b = self.e2_mul(ac, &a.e1, e1);
        let tmp = self.e2_add(ac, &a.e1, &a.e2);
        let t1 = self.e2_mul(ac, &tmp, e1);
        let t1 = self.e2_sub(ac, &t1, &b_b);
        let t1 = self.e2_mul_by_non_residue(ac, &t1);
        let t1 = self.e2_add(ac, &t1, &a_a);
        let tmp = self.e2_add(ac, &a.e0, &a.e2);
        let t3 = self.e2_mul(ac, &tmp, e0);
        let t3 = self.e2_sub(ac, &t3, &a_a);
        let t3 = self.e2_add(ac, &t3, &b_b);
        let t2 = self.e2_add(ac, e0, e1);
        let tmp = self.e2_add(ac, &a.e0, &a.e1);
        let t2 = self.e2_mul(ac, &tmp, &t2);
        let t2 = self.e2_sub(ac, &t2, &a_a);
        let t2 = self.e2_sub(ac, &t2, &b_b);

        E6 {
            e0: t1,
            e1: t2,
            e2: t3,
        }
    }

    pub(crate) fn e6_mul_by_non_residue(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E6<VarBig<N>>,
    ) -> E6<VarBig<N>> {
        let t0 = self.e2_mul_by_non_residue(ac, &a.e2);

        E6 {
            e0: t0,
            e1: a.e0.clone(),
            e2: a.e1.clone(),
        }
    }

    pub(crate) fn e6_frobenius_map(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E6<VarBig<N>>,
        power: usize,
    ) -> E6<VarBig<N>> {
        let e0 = self.e2_frobenius_map(ac, &a.e0, power);
        let e1 = self.e2_frobenius_map(ac, &a.e1, power);
        let e2 = self.e2_frobenius_map(ac, &a.e2, power);
        let e1 = self.e2_mul_constant(ac, &e1, &self.frobenius61[power % 6]);
        let e2 = self.e2_mul_constant(ac, &e2, &self.frobenius62[power % 6]);
        E6 { e0, e1, e2 }
    }
}
