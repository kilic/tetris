use crate::{
    gadget::{
        big_field::{Big, VarBig},
        ecc::Curve,
    },
    ir::ac::AbstractCircuit,
    Error, Field, Value, Var,
};
use num_bigint::BigUint;
use num_traits::One;
use num_traits::Zero;

use super::{witness::Bw6Pairing, Bw6PairingGadget};

#[derive(Clone, Debug)]
pub struct E3<N> {
    pub(crate) e0: N,
    pub(crate) e1: N,
    pub(crate) e2: N,
}

impl<N> E3<N> {
    pub(crate) fn new(e0: N, e1: N, e2: N) -> Self {
        Self { e0, e1, e2 }
    }
}

impl<N: Field> E3<VarBig<N>> {
    pub(crate) fn value(&self) -> Value<E3<BigUint>> {
        self.e0
            .uint()
            .zip(self.e1.uint())
            .zip(self.e2.uint())
            .map(|((e0, e1), e2)| E3 {
                e0: e0.clone(),
                e1: e1.clone(),
                e2: e2.clone(),
            })
    }
}

impl<N: Field, G1: Curve, G2: Curve, Pairing: Bw6Pairing> Bw6PairingGadget<N, G1, G2, Pairing> {
    pub fn e3_assign(
        &self,
        ac: &mut AbstractCircuit<N>,
        e: Value<E3<BigUint>>,
    ) -> Result<E3<VarBig<N>>, Error> {
        let e0 = self.assign_base_field(ac, e.as_ref().map(|e| &e.e0))?;
        let e1 = self.assign_base_field(ac, e.as_ref().map(|e| &e.e1))?;
        let e2 = self.assign_base_field(ac, e.as_ref().map(|e| &e.e2))?;
        Ok(E3 { e0, e1, e2 })
    }

    pub(crate) fn e3_add(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E3<VarBig<N>>,
        b: &E3<VarBig<N>>,
    ) -> E3<VarBig<N>> {
        E3 {
            e0: a.e0.add(ac, &b.e0),
            e1: a.e1.add(ac, &b.e1),
            e2: a.e2.add(ac, &b.e2),
        }
    }

    pub(crate) fn e3_add_constant(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E3<VarBig<N>>,
        b: &E3<Big<N>>,
    ) -> E3<VarBig<N>> {
        E3 {
            e0: a.e0.add_constant(ac, &b.e0),
            e1: a.e1.add_constant(ac, &b.e1),
            e2: a.e2.add_constant(ac, &b.e2),
        }
    }

    pub(crate) fn e3_normal_equal(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E3<VarBig<N>>,
        b: &E3<VarBig<N>>,
    ) -> Result<(), Error> {
        self.base_field_crt.normal_equal(ac, &a.e0, &b.e0)?;
        self.base_field_crt.normal_equal(ac, &a.e1, &b.e1)?;
        self.base_field_crt.normal_equal(ac, &a.e2, &b.e2)?;
        Ok(())
    }

    pub(crate) fn e3_assert_zero(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E3<VarBig<N>>,
    ) -> Result<(), Error> {
        self.base_field_crt.assert_zero(ac, &a.e0)?;
        self.base_field_crt.assert_zero(ac, &a.e1)?;
        Ok(())
    }

    pub(crate) fn e3_select(
        &self,
        ac: &mut AbstractCircuit<N>,
        cond: &Var<N>,
        e0: &E3<VarBig<N>>,
        e1: &E3<VarBig<N>>,
    ) -> Result<E3<VarBig<N>>, Error> {
        let t0 = e0.e0.select(ac, cond, &e1.e0)?;
        let t1 = e0.e1.select(ac, cond, &e1.e1)?;
        let t2 = e0.e2.select(ac, cond, &e1.e2)?;
        Ok(E3 {
            e0: t0,
            e1: t1,
            e2: t2,
        })
    }

    pub(crate) fn e3_reduce(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E3<VarBig<N>>,
    ) -> E3<VarBig<N>> {
        E3 {
            e0: self.base_field_crt.reduce(ac, &a.e0),
            e1: self.base_field_crt.reduce(ac, &a.e1),
            e2: self.base_field_crt.reduce(ac, &a.e2),
        }
    }

    pub(crate) fn e3_constant(
        &self,
        ac: &mut AbstractCircuit<N>,
        constant: &E3<BigUint>,
    ) -> Result<E3<VarBig<N>>, Error> {
        let e0 = self.base_field_crt.get_constant(ac, &constant.e0)?;
        let e1 = self.base_field_crt.get_constant(ac, &constant.e1)?;
        let e2 = self.base_field_crt.get_constant(ac, &constant.e2)?;
        Ok(E3 { e0, e1, e2 })
    }

    pub(crate) fn e3_one(&self, ac: &mut AbstractCircuit<N>) -> E3<VarBig<N>> {
        let one = self
            .base_field_crt
            .get_constant(ac, &BigUint::one())
            .unwrap();
        let zero = self
            .base_field_crt
            .get_constant(ac, &BigUint::zero())
            .unwrap();
        E3 {
            e0: one,
            e1: zero.clone(),
            e2: zero,
        }
    }

    pub(crate) fn e3_zero(&self, ac: &mut AbstractCircuit<N>) -> E3<VarBig<N>> {
        let zero = self
            .base_field_crt
            .get_constant(ac, &BigUint::zero())
            .unwrap();
        E3 {
            e0: zero.clone(),
            e1: zero.clone(),
            e2: zero,
        }
    }

    pub(crate) fn e3_double(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E3<VarBig<N>>,
    ) -> E3<VarBig<N>> {
        E3 {
            e0: a.e0.double(ac),
            e1: a.e1.double(ac),
            e2: a.e2.double(ac),
        }
    }

    pub(crate) fn e3_sub(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E3<VarBig<N>>,
        b: &E3<VarBig<N>>,
    ) -> E3<VarBig<N>> {
        E3 {
            e0: a.e0.sub(ac, &b.e0),
            e1: a.e1.sub(ac, &b.e1),
            e2: a.e2.sub(ac, &b.e2),
        }
    }

    pub(crate) fn e3_neg(&self, ac: &mut AbstractCircuit<N>, a: &E3<VarBig<N>>) -> E3<VarBig<N>> {
        E3 {
            e0: self.base_field_crt.neg(ac, &a.e0),
            e1: self.base_field_crt.neg(ac, &a.e1),
            e2: self.base_field_crt.neg(ac, &a.e2),
        }
    }

    pub(crate) fn e3_mul_by_01(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E3<VarBig<N>>,
        e0: &VarBig<N>,
        e1: &VarBig<N>,
    ) -> E3<VarBig<N>> {
        let crt = &self.base_field_crt;
        let aa = crt.mul(ac, &a.e0, e0, &[], &[]);
        let bb = crt.mul(ac, &a.e1, e1, &[], &[]);
        let tmp = &a.e1.add(ac, &a.e2);

        let t1 = &crt.mul(ac, tmp, e1, &[], &[&bb]);
        let t1 = self.mul_by_non_residue(ac, t1);
        let t1 = t1.add(ac, &aa);

        let tmp = &a.e0.add(ac, &a.e2);
        let t3 = crt.mul(ac, tmp, e0, &[&bb], &[&aa]);

        let t2 = e0.add(ac, e1);
        let tmp = &a.e0.add(ac, &a.e1);
        let t2 = crt.mul(ac, tmp, &t2, &[], &[&aa, &bb]);

        let ret = E3 {
            e0: t1,
            e1: t2,
            e2: t3,
        };

        // #[cfg(test)]
        // {
        //     let e0 = crt.reduce(ac, e0);
        //     let e1 = crt.reduce(ac, e1);
        //     let b = e0.uint().zip(e1.uint()).map(|(e0, e1)| {
        //         let e0 = e0.clone();
        //         let e1 = e1.clone();
        //         let e2 = BigUint::zero();
        //         let b: Fq3 = (&E3 { e0, e1, e2 }).into();
        //         b
        //     });
        //     let a = self.e3_reduce(ac, &a);
        //     let a = a.value().map(|a| {
        //         let a: Fq3 = (&a).into();
        //         a
        //     });
        //     let ret = self.e3_reduce(ac, &ret);
        //     let ret = ret.value().map(|ret| {
        //         let ret: Fq3 = (&ret).into();
        //         ret
        //     });
        //     (a * b).zip(ret).map(|(c0, c1)| {
        //         assert_eq!(c0, c1);
        //     });
        // }

        ret
    }

    pub(crate) fn mul_by_non_residue(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &VarBig<N>,
    ) -> VarBig<N> {
        let a = a.double(ac);
        let a = a.double(ac);
        self.base_field_crt.neg(ac, &a)
    }

    // pub(crate) fn e3_square(
    //     &self,
    //     ac: &mut AbstractCircuit<N>,
    //     a: &E3<VarBig<N>>,
    // ) -> E3<VarBig<N>> {
    //     let crt = &self.base_field_crt;
    //     let s0 = crt.square(ac, &a.e0, &[], &[]);

    //     let s1 = a.e0.add(ac, &a.e1);
    //     let s1 = s1.double(ac);

    //     let s2 = a.e0.add(ac, &a.e2);
    //     let s2 = s2.sub(ac, &a.e1);
    //     let s2 = crt.square(ac, &s2, &[], &[]);

    //     let s3 = a.e1.add(ac, &a.e2);
    //     let s3 = s3.double(ac);

    //     let s4 = crt.square(ac, &a.e2, &[], &[]);

    //     let e0 = self.mul_by_non_residue(ac, &s3);
    //     let e0 = e0.add(ac, &s0);

    //     let e1 = self.mul_by_non_residue(ac, &s4);
    //     let e1 = e1.add(ac, &s1);

    //     let e2 = s1.add(ac, &s2);
    //     let e2 = e2.add(ac, &s3);
    //     let e2 = e2.sub(ac, &s0);
    //     let e2 = e2.sub(ac, &s4);

    //     let ret = E3 { e0, e1, e2 };

    //     // #[cfg(test)]
    //     // {
    //     //     let a = self.e3_reduce(ac, a);
    //     //     let ret = self.e3_reduce(ac, &ret);
    //     //     let a = a.value().map(|a| {
    //     //         let a: Fq3 = (&a).into();
    //     //         a
    //     //     });
    //     //     let ret = ret.value().map(|ret| {
    //     //         let ret: Fq3 = (&ret).into();
    //     //         ret
    //     //     });
    //     //     (a * a).zip(ret).map(|(c0, c1)| {
    //     //         assert_eq!(c0, c1);
    //     //     });
    //     // }

    //     ret
    // }

    pub(crate) fn e3_mul(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E3<VarBig<N>>,
        b: &E3<VarBig<N>>,
    ) -> E3<VarBig<N>> {
        let crt = &self.base_field_crt;
        let t0 = crt.mul(ac, &a.e0, &b.e0, &[], &[]);
        let t1 = crt.mul(ac, &a.e1, &b.e1, &[], &[]);
        let t2 = crt.mul(ac, &a.e2, &b.e2, &[], &[]);

        let t3 = a.e1.add(ac, &a.e2);
        let t4 = b.e1.add(ac, &b.e2);

        let t3 = crt.mul(ac, &t3, &t4, &[], &[&t1, &t2]);
        let t3 = self.mul_by_non_residue(ac, &t3);
        let e0 = t0.add(ac, &t3);

        let t3 = a.e0.add(ac, &a.e1);
        let t4 = b.e0.add(ac, &b.e1);

        let t3 = crt.mul(ac, &t3, &t4, &[], &[&t0, &t1]);
        let t4 = self.mul_by_non_residue(ac, &t2);
        let e1 = t3.add(ac, &t4);

        let t3 = a.e0.add(ac, &a.e2);
        let t4 = b.e0.add(ac, &b.e2);
        let e2 = crt.mul(ac, &t3, &t4, &[&t1], &[&t0, &t2]);

        let ret = E3 { e0, e1, e2 };

        // #[cfg(test)]
        // {
        //     let a = self.e3_reduce(ac, a);
        //     let b = self.e3_reduce(ac, b);
        //     let ret = self.e3_reduce(ac, &ret);
        //     let a = a.value().map(|a| {
        //         let a: Fq3 = (&a).into();
        //         a
        //     });
        //     let b = b.value().map(|b| {
        //         let b: Fq3 = (&b).into();
        //         b
        //     });
        //     let ret = ret.value().map(|ret| {
        //         let ret: Fq3 = (&ret).into();
        //         ret
        //     });
        //     (a * b).zip(ret).map(|(c0, c1)| {
        //         assert_eq!(c0, c1);
        //     });
        // }

        ret
    }

    pub(crate) fn e3_mul_constant(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E3<VarBig<N>>,
        b: &Big<N>,
    ) -> E3<VarBig<N>> {
        let crt = &self.base_field_crt;
        let e0 = crt.mul_constant(ac, &a.e0, b, &[], &[]);
        let e1 = crt.mul_constant(ac, &a.e1, b, &[], &[]);
        let e2 = crt.mul_constant(ac, &a.e2, b, &[], &[]);

        E3 { e0, e1, e2 }
    }

    pub(crate) fn e3_mul_by_non_residue(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E3<VarBig<N>>,
    ) -> E3<VarBig<N>> {
        let e0 = self.mul_by_non_residue(ac, &a.e2);
        let e1 = a.e0.clone();
        let e2 = a.e1.clone();
        E3 { e0, e1, e2 }
    }

    pub(crate) fn e3_frobenius(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &E3<VarBig<N>>,
    ) -> E3<VarBig<N>> {
        let e0 = a.e0.clone();
        let e1 = self
            .base_field_crt
            .mul_constant(ac, &a.e1, &self.frobenius_3c1, &[], &[]);
        let e2 = self
            .base_field_crt
            .mul_constant(ac, &a.e2, &self.frobenius_3c2, &[], &[]);
        E3 { e0, e1, e2 }
    }
}
