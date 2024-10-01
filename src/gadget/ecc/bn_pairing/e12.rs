use super::{e2::E2, e6::E6, witness::BNPairing, BNPairingGadget};
use crate::{gadget::big_field::VarBig, ir::ac::AbstractCircuit, Error, Field, Value, Var};
use num_bigint::BigUint;

#[derive(Clone, Debug)]
pub struct E12<N> {
    pub(crate) e0: E6<N>,
    pub(crate) e1: E6<N>,
}

impl<N> E12<N> {
    pub(crate) fn new(e0: E6<N>, e1: E6<N>) -> Self {
        Self { e0, e1 }
    }
}

impl<N: Field> E12<VarBig<N>> {
    pub(crate) fn value(&self) -> Value<E12<BigUint>> {
        self.e0
            .value()
            .zip(self.e1.value())
            .map(|(e0, e1)| E12 { e0, e1 })
    }
}

impl<N: Field, BNPairingEngine: BNPairing> BNPairingGadget<N, BNPairingEngine> {
    pub(crate) fn e12_one(&self, ac: &mut AbstractCircuit<N>) -> E12<VarBig<N>> {
        E12 {
            e0: self.e6_one(ac),
            e1: self.e6_zero(ac),
        }
    }

    pub(crate) fn e12_constant(
        &self,
        ac: &mut AbstractCircuit<N>,
        e: E12<BigUint>,
    ) -> Result<E12<VarBig<N>>, Error> {
        Ok(E12 {
            e0: self.e6_constant(ac, e.e0)?,
            e1: self.e6_constant(ac, e.e1)?,
        })
    }

    pub(crate) fn e12_reduce(
        &self,
        ac: &mut AbstractCircuit<N>,
        e: &E12<VarBig<N>>,
    ) -> E12<VarBig<N>> {
        E12 {
            e0: self.e6_reduce(ac, &e.e0),
            e1: self.e6_reduce(ac, &e.e1),
        }
    }

    pub(crate) fn e12_sub(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E12<VarBig<N>>,
        b: &E12<VarBig<N>>,
    ) -> E12<VarBig<N>> {
        let e0 = self.e6_sub(ac, &a.e0, &b.e0);
        let e1 = self.e6_sub(ac, &a.e1, &b.e1);
        E12 { e0, e1 }
    }

    pub(crate) fn e12_assign(
        &self,
        ac: &mut AbstractCircuit<N>,
        e: Value<E12<BigUint>>,
    ) -> Result<E12<VarBig<N>>, Error> {
        Ok(E12 {
            e0: self.e6_assign(ac, e.as_ref().map(|e| e.e0.clone()))?,
            e1: self.e6_assign(ac, e.as_ref().map(|e| e.e1.clone()))?,
        })
    }

    pub(crate) fn e12_select(
        &self,
        ac: &mut AbstractCircuit<N>,
        cond: &Var<N>,
        e0: &E12<VarBig<N>>,
        e1: &E12<VarBig<N>>,
    ) -> Result<E12<VarBig<N>>, Error> {
        let t0 = self.e6_select(ac, cond, &e0.e0, &e1.e0)?;
        let t1 = self.e6_select(ac, cond, &e0.e1, &e1.e1)?;
        Ok(E12 { e0: t0, e1: t1 })
    }

    pub(crate) fn e12_mul(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E12<VarBig<N>>,
        b: &E12<VarBig<N>>,
    ) -> E12<VarBig<N>> {
        let t = self.e6_mul(ac, &a.e0, &b.e0);
        let t1 = self.e6_mul(ac, &a.e1, &b.e1);
        let t2 = self.e6_add(ac, &b.e0, &b.e1);
        let e1 = self.e6_add(ac, &a.e1, &a.e0);
        let e1 = self.e6_mul(ac, &e1, &t2);
        let e1 = self.e6_sub(ac, &e1, &t);
        let e1 = self.e6_sub(ac, &e1, &t1);
        let t1 = self.e6_mul_by_non_residue(ac, &t1);
        let e0 = self.e6_add(ac, &t, &t1);
        E12 { e0, e1 }
    }

    pub(crate) fn e12_square(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E12<VarBig<N>>,
    ) -> E12<VarBig<N>> {
        let t0 = self.e6_add(ac, &a.e0, &a.e1);
        let t2 = self.e6_mul(ac, &a.e0, &a.e1);
        let t1 = self.e6_mul_by_non_residue(ac, &a.e1);
        let t1 = self.e6_add(ac, &t1, &a.e0);
        let t3 = self.e6_mul_by_non_residue(ac, &t2);
        let t0 = self.e6_mul(ac, &t0, &t1);
        let t0 = self.e6_sub(ac, &t0, &t2);
        let e0 = self.e6_sub(ac, &t0, &t3);
        let e1 = self.e6_double(ac, &t2);
        E12 { e0, e1 }
    }

    pub(crate) fn e12_mul_sparse(
        &self,
        ac: &mut AbstractCircuit<N>,
        f: &mut E12<VarBig<N>>,
        e0: &E2<VarBig<N>>,
        e1: &E2<VarBig<N>>,
    ) {
        let t0 = self.e6_mul_by_01(ac, &f.e1, e0, e1);
        let t0 = self.e6_mul_by_non_residue(ac, &t0);
        let x0 = self.e6_add(ac, &t0, &f.e0);

        let t1 = self.e6_mul_by_01(ac, &f.e0, e0, e1);
        let x1 = self.e6_add(ac, &t1, &f.e1);

        f.e0 = x0;
        f.e1 = x1;
    }

    pub(crate) fn e12_frobenius_map(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E12<VarBig<N>>,
        power: usize,
    ) -> E12<VarBig<N>> {
        let e0 = self.e6_frobenius_map(ac, &a.e0, power);
        let e1 = self.e6_frobenius_map(ac, &a.e1, power);

        match power {
            0 => E12 { e0, e1 },
            6 => {
                let e1 = self.e6_neg(ac, &e1);
                E12 { e0, e1 }
            }
            _ => {
                let t0 = self.e2_mul_constant(ac, &e1.e0, &self.frobenius12[power]);
                let t1 = self.e2_mul_constant(ac, &e1.e1, &self.frobenius12[power]);
                let t2 = self.e2_mul_constant(ac, &e1.e2, &self.frobenius12[power]);
                let e1 = E6 {
                    e0: t0,
                    e1: t1,
                    e2: t2,
                };
                E12 { e0, e1 }
            }
        }
    }

    pub(crate) fn e12_assert_zero(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E12<VarBig<N>>,
    ) -> Result<(), Error> {
        self.e6_assert_zero(ac, &a.e0)?;
        self.e6_assert_zero(ac, &a.e1)?;
        Ok(())
    }

    pub(crate) fn e12_inverse(
        &self,
        ac: &mut AbstractCircuit<N>,
        e: &E12<VarBig<N>>,
    ) -> Result<E12<VarBig<N>>, Error> {
        let inv_e = BNPairingEngine::e12_inverse(e)?;
        let inv_e = self.e12_assign(ac, inv_e).unwrap();
        let must_be_one = self.e12_mul(ac, e, &inv_e);
        let one = self.e12_one(ac);
        let must_be_zero = self.e12_sub(ac, &must_be_one, &one);
        self.e12_assert_zero(ac, &must_be_zero)?;
        Ok(inv_e)
    }
}
