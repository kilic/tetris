use super::{ecc_general::GeneralEccGadget, Point};
use crate::{
    gadget::{
        big_field::VarBig,
        ecc::{msm::EccMulGadget, Coordinates, Curve, EccGadget},
    },
    ir::ac::AbstractCircuit,
    Error, Field,
};

pub struct EcdsaSignature<N: Field> {
    pub r: VarBig<N>,
    pub s: VarBig<N>,
}

pub type PublicKey<N> = Point<VarBig<N>>;

impl<C: Curve, N: Field> GeneralEccGadget<C, N> {
    pub fn ecdsa_assert_verify(
        &self,
        ac: &mut AbstractCircuit<N>,
        generator: C,
        public_key: &PublicKey<N>,
        message_hash: &VarBig<N>,
        signature: &EcdsaSignature<N>,
    ) -> Result<(), Error> {
        // 1. check 0 < r, s < n
        // since `assert_not_zero` already includes a in-field check, we can just
        // call `assert_not_zero`
        self.scalar_field.assert_not_zero(ac, &signature.r)?;
        self.scalar_field.assert_not_zero(ac, &signature.s)?;

        // 2. w = s^(-1) (mod n)
        // 3. u1 = m' * w (mod n)
        let u1 = self.scalar_field.div(ac, message_hash, &signature.s);

        // 4. u2 = r * w (mod n)
        let u2 = self.scalar_field.div(ac, &signature.r, &signature.s);

        // 5. compute Q = u1*G + u2*pk
        let u1_g = self.msm_fix_vertical_extended_mem(ac, 4, &[generator], &[u1]);
        let u2_pk = self.msm_var_vertical_with_mem(ac, 4, &[public_key.clone()], &[u2]);

        let q = self.add_incomplete(ac, &u1_g, &u2_pk);

        // 6 .cast base field q_x as scalar field
        // WARNING:
        // assumes same number of limbs are used in base and scalar field
        assert_eq!(
            self.scalar_field.rns.n_limbs(),
            self.base_field.rns.n_limbs()
        );

        let q_x = q.x();
        let q_x_reduced = self.scalar_field.reduce(ac, q_x);

        q_x_reduced.copy_equal(ac, &signature.r)?;

        Ok(())
    }
}
