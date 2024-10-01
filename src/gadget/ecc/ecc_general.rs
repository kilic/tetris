use num_bigint::BigUint;

use super::msm::EccMulGadget;
use super::Curve;
use super::EccGadget;
use crate::gadget::big_field::crt::CrtGadget;
use crate::gadget::big_field::Big;
use crate::ir::combination::quad::Qc;
use crate::ir::combination::CombinationGadget;
use crate::qc;
use crate::Error;
use crate::Field;
use crate::{
    gadget::big_field::{rns::Range, VarBig},
    ir::ac::AbstractCircuit,
    witness::Var,
    Value,
};
use std::marker::PhantomData;

pub struct GeneralEccGadget<C: Curve, N: Field> {
    pub(crate) scalar_field: CrtGadget<N>,
    pub(crate) base_field: CrtGadget<N>,
    pub(crate) b: Big<N>,
    _marker: PhantomData<C>,
}

impl<C: Curve, N: Field> GeneralEccGadget<C, N> {
    pub fn new(
        scalar_limb_size: usize,
        scalar_mod: &BigUint,
        base_limb_size: usize,
        base_mod: &BigUint,
        sublimb_size: usize,
    ) -> Self {
        let base_field = CrtGadget::new(base_limb_size, sublimb_size, base_mod);
        let scalar_field = CrtGadget::new(scalar_limb_size, sublimb_size, scalar_mod);
        let b = base_field.rns.big_from_uint(&C::b());
        Self {
            scalar_field,
            base_field,
            b,
            _marker: PhantomData,
        }
    }
}

impl<C: Curve, N: Field> EccGadget<C, N> for GeneralEccGadget<C, N> {
    type Scalar = VarBig<N>;

    fn base_field_crt(&self) -> &CrtGadget<N> {
        &self.base_field
    }

    fn b(&self) -> &Big<N> {
        &self.b
    }

    fn assign_scalar(
        &self,
        ac: &mut AbstractCircuit<N>,
        scalar: &Value<C::Scalar>,
    ) -> Self::Scalar {
        let scalar = scalar.map(|e| e.uint());
        self.scalar_field
            .assign(ac, scalar.as_ref(), &Range::Remainder)
            .unwrap()
    }

    fn decompose_scalar(
        &self,
        ac: &mut AbstractCircuit<N>,
        window: usize,
        scalar: &Self::Scalar,
    ) -> Result<Vec<Var<N>>, Error> {
        assert!(window > 0);
        let limb_sizes = self.scalar_field.rns.limb_sizes(&Range::Remainder);
        let scalar = scalar
            .limbs()
            .zip(limb_sizes)
            .map(|(limb, limb_size)| ac.decompose(1, limb_size, limb.var()))
            .collect::<Result<Vec<_>, Error>>();

        let scalar = scalar.unwrap();
        let scalar = scalar.into_iter().flatten().collect::<Vec<_>>();

        if window == 1 {
            Ok(scalar)
        } else {
            let bases = (0..window)
                .map(|i| N::from_u64((1 << i) as u64))
                .collect::<Vec<_>>();
            Ok(scalar
                .chunks(window)
                .map(|chunk| {
                    let qc = chunk.iter().zip(bases.iter()).map(|(bit, base)| bit * base);
                    ac.eval(qc!() + qc)
                })
                .collect())
        }
    }
}

impl<C: Curve, N: Field> EccMulGadget<C, N> for GeneralEccGadget<C, N> where C::Base: Field {}
