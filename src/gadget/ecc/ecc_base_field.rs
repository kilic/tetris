use num_bigint::BigUint;

use super::{msm::EccMulGadget, Curve, EccGadget};
use crate::{
    gadget::big_field::{crt::CrtGadget, Big},
    ir::ac::AbstractCircuit,
    witness::Var,
    Error, Field, Value,
};

pub struct BaseFieldEccGadget<C: Curve> {
    crt: CrtGadget<C::Scalar>,
    b: Big<C::Scalar>,
}

impl<C: Curve> BaseFieldEccGadget<C> {
    pub fn new(limb_size: usize, wrong_mod: &BigUint, sublimb_size: usize) -> Self {
        let crt = CrtGadget::new(limb_size, sublimb_size, wrong_mod);
        let b = crt.rns.big_from_uint(&C::b());
        Self { b, crt }
    }
}

impl<C: Curve> EccGadget<C, C::Scalar> for BaseFieldEccGadget<C> {
    type Scalar = Var<C::Scalar>;

    fn base_field_crt(&self) -> &CrtGadget<C::Scalar> {
        &self.crt
    }

    fn b(&self) -> &Big<C::Scalar> {
        &self.b
    }

    fn assign_scalar(
        &self,
        ac: &mut AbstractCircuit<C::Scalar>,
        scalar: &Value<C::Scalar>,
    ) -> Self::Scalar {
        ac.assign(scalar)
    }

    fn decompose_scalar(
        &self,
        ac: &mut AbstractCircuit<C::Scalar>,
        window: usize,
        scalar: &Self::Scalar,
    ) -> Result<Vec<Var<C::Scalar>>, Error> {
        use crate::witness::field::Field;
        ac.decompose(window, C::Scalar::num_bits(), scalar)
    }
}

impl<C: Curve> EccMulGadget<C, C::Scalar> for BaseFieldEccGadget<C> where C::Base: Field {}
