use super::{e3::E3, witness::Bw6Pairing, Bw6PairingGadget};
use crate::{
    gadget::{big_field::VarBig, ecc::Curve},
    ir::ac::AbstractCircuit,
    Error, Field, Value,
};
use num_bigint::BigUint;

#[derive(Clone, Debug)]
pub struct E6<N> {
    pub(crate) e0: E3<N>,
    pub(crate) e1: E3<N>,
}

impl<N> E6<N> {
    pub(crate) fn new(e0: E3<N>, e1: E3<N>) -> Self {
        Self { e0, e1 }
    }
}

impl<N: Field> E6<VarBig<N>> {
    pub(crate) fn value(&self) -> Value<E6<BigUint>> {
        self.e0
            .value()
            .zip(self.e1.value())
            .map(|(e0, e1)| E6 { e0, e1 })
    }
}

impl<N: Field, G1: Curve, G2: Curve, Pairing: Bw6Pairing> Bw6PairingGadget<N, G1, G2, Pairing> {
    pub(crate) fn e6_one(&self, ac: &mut AbstractCircuit<N>) -> E6<VarBig<N>> {
        E6 {
            e0: self.e3_one(ac),
            e1: self.e3_zero(ac),
        }
    }

    // pub(crate) fn e6_reduce(
    //     &self,
    //     ac: &mut AbstractCircuit<N>,
    //     e: &E6<VarBig<N>>,
    // ) -> E6<VarBig<N>> {
    //     E6 {
    //         e0: self.e3_reduce(ac, &e.e0),
    //         e1: self.e3_reduce(ac, &e.e1),
    //     }
    // }

    pub(crate) fn e6_sub(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E6<VarBig<N>>,
        b: &E6<VarBig<N>>,
    ) -> E6<VarBig<N>> {
        let e0 = self.e3_sub(ac, &a.e0, &b.e0);
        let e1 = self.e3_sub(ac, &a.e1, &b.e1);
        E6 { e0, e1 }
    }

    pub(crate) fn e6_assign(
        &self,
        ac: &mut AbstractCircuit<N>,
        e: Value<E6<BigUint>>,
    ) -> Result<E6<VarBig<N>>, Error> {
        Ok(E6 {
            e0: self.e3_assign(ac, e.as_ref().map(|e| e.e0.clone()))?,
            e1: self.e3_assign(ac, e.as_ref().map(|e| e.e1.clone()))?,
        })
    }

    pub(crate) fn e6_mul(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E6<VarBig<N>>,
        b: &E6<VarBig<N>>,
    ) -> E6<VarBig<N>> {
        let t = self.e3_mul(ac, &a.e0, &b.e0);
        let t1 = self.e3_mul(ac, &a.e1, &b.e1);
        let t2 = self.e3_add(ac, &b.e0, &b.e1);
        let e1 = self.e3_add(ac, &a.e1, &a.e0);
        let e1 = self.e3_mul(ac, &e1, &t2);
        let e1 = self.e3_sub(ac, &e1, &t);
        let e1 = self.e3_sub(ac, &e1, &t1);
        let t1 = self.e3_mul_by_non_residue(ac, &t1);
        let e0 = self.e3_add(ac, &t, &t1);
        E6 { e0, e1 }
    }

    pub(crate) fn e6_square(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E6<VarBig<N>>,
    ) -> E6<VarBig<N>> {
        let t0 = self.e3_add(ac, &a.e0, &a.e1);
        let t2 = self.e3_mul(ac, &a.e0, &a.e1);
        let t1 = self.e3_mul_by_non_residue(ac, &a.e1);
        let t1 = self.e3_add(ac, &t1, &a.e0);
        let t3 = self.e3_mul_by_non_residue(ac, &t2);
        let t0 = self.e3_mul(ac, &t0, &t1);
        let t0 = self.e3_sub(ac, &t0, &t2);
        let e0 = self.e3_sub(ac, &t0, &t3);
        let e1 = self.e3_double(ac, &t2);
        E6 { e0, e1 }
    }

    pub(crate) fn e6_mul_sparse(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &mut E6<VarBig<N>>,
        e0: &VarBig<N>,
        e1: &VarBig<N>,
    ) {
        let t0 = self.e3_mul_by_01(ac, &a.e0, e0, e1);
        let t1 = self.e3_mul_by_01(ac, &a.e1, e0, e1);
        let v0 = self.e3_mul_by_non_residue(ac, &a.e1);
        let v0 = self.e3_mul_by_non_residue(ac, &v0);
        let v1 = self.e3_mul_by_non_residue(ac, &a.e0);
        let u0 = self.e3_add(ac, &t0, &v0);
        let u1 = self.e3_add(ac, &t1, &v1);

        // #[cfg(test)]
        // {
        //     let e0 = self.base_field_crt.reduce(ac, e0);
        //     let e1 = self.base_field_crt.reduce(ac, e1);
        //     let b = e0.uint().zip(e1.uint()).map(|(e0, e1)| {
        //         let e0 = e0.clone();
        //         let e1 = e1.clone();
        //         let e2 = BigUint::from(0usize);
        //         let c0: Fq3 = (&E3 { e0, e1, e2 }).into();
        //         let c1: Fq3 = Fq3::new(Fq::zero(), Fq::one(), Fq::zero());
        //         Fq6::new(c0, c1)
        //     });
        //     let a = self.e6_reduce(ac, a);
        //     let a = a.value().map(|a| {
        //         let a: Fq6 = (&a).into();
        //         a
        //     });

        //     let u0 = self.e3_reduce(ac, &u0);
        //     let u1 = self.e3_reduce(ac, &u1);
        //     let ret = u0.value().zip(u1.value()).map(|(e0, e1)| {
        //         let ret: Fq6 = (&E6 { e0, e1 }).into();
        //         ret
        //     });

        //     (a * b).zip(ret).map(|(c0, c1)| {
        //         assert_eq!(c0, c1);
        //     });
        // }

        a.e0 = u0;
        a.e1 = u1;
    }

    pub(crate) fn e6_frobenius_map(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E6<VarBig<N>>,
    ) -> E6<VarBig<N>> {
        let e0 = self.e3_frobenius(ac, &a.e0);
        let e1 = self.e3_frobenius(ac, &a.e1);
        let e1 = self.e3_mul_constant(ac, &e1, &self.frobenius_6c1);
        E6 { e0, e1 }
    }

    pub(crate) fn e6_assert_zero(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E6<VarBig<N>>,
    ) -> Result<(), Error> {
        self.e3_assert_zero(ac, &a.e0)?;
        self.e3_assert_zero(ac, &a.e1)?;
        Ok(())
    }

    pub(crate) fn e6_inverse(
        &self,
        ac: &mut AbstractCircuit<N>,
        e: &E6<VarBig<N>>,
    ) -> Result<E6<VarBig<N>>, Error> {
        let inv_e = Pairing::e6_inverse(e)?;
        let inv_e = self.e6_assign(ac, inv_e).unwrap();
        let must_be_one = self.e6_mul(ac, e, &inv_e);
        let one = self.e6_one(ac);
        let must_be_zero = self.e6_sub(ac, &must_be_one, &one);
        self.e6_assert_zero(ac, &must_be_zero)?;
        Ok(inv_e)
    }
}
