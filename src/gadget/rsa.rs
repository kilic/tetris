use super::{
    big_field::{crt_var::VarCrtGadget, rns::Range, VarBig},
    sha256::{HashInWords, Sha256Gadget},
    VarByte,
};
use crate::{ir::ac::AbstractCircuit, Error, Field, Value};
use num_bigint::BigUint;

const KEY_BITS: usize = 2048;

pub struct RsaGadget<N: Field> {
    crt: VarCrtGadget<N>,
    sha256: Sha256Gadget<N>,
    fixed_part: Vec<N>,
}

impl<N: Field> RsaGadget<N> {
    pub fn new(
        ac: &mut AbstractCircuit<N>,
        limb_size: usize,
        sublimb_size: usize,
        pubkey_n: Value<&BigUint>,
    ) -> Result<Self, Error> {
        let crt = VarCrtGadget::new(ac, KEY_BITS, limb_size, sublimb_size, pubkey_n)?;
        let mut fixed_part: Vec<u8> = vec![];
        fixed_part.extend_from_slice(&[0, 1]);
        fixed_part.extend_from_slice(&[0xff; 202]);
        fixed_part.extend_from_slice(&[0]);
        fixed_part.extend_from_slice(&[
            0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
            0x01, 0x05, 0x00, 0x04, 0x20,
        ]);
        assert_eq!(fixed_part.len(), KEY_BITS / 8 - 32);
        let fixed_part = fixed_part
            .into_iter()
            .map(|e| N::from_u64(e as u64))
            .collect();
        Ok(Self {
            crt,
            fixed_part,
            sha256: Sha256Gadget::new(ac),
        })
    }

    pub fn verify(
        &self,
        ac: &mut AbstractCircuit<N>,
        msg: &Value<Vec<u8>>,
        msg_len: usize,
        sig: Value<&BigUint>,
    ) -> Result<(), Error> {
        let msg = VarByte::assign_many(ac, msg, msg_len);
        let hash = self.sha256.hash(ac, &msg);
        let sig = self.crt.assign(ac, sig, &Range::Remainder)?;
        let padded = self.pow(ac, sig);
        self.cmp(ac, &hash, &padded)?;
        Ok(())
    }

    fn pow(&self, ac: &mut AbstractCircuit<N>, sig: VarBig<N>) -> VarBig<N> {
        let mut acc = sig.clone();
        (0..16).for_each(|_| acc = self.crt.square(ac, &acc, &[], &[]));
        self.crt.mul(ac, &acc, &sig, &[], &[])
    }

    fn cmp(
        &self,
        ac: &mut AbstractCircuit<N>,
        hash: &HashInWords<N>,
        padded: &VarBig<N>,
    ) -> Result<(), Error> {
        let padded = self.crt.to_bytes(ac, padded);
        self.fixed_part
            .iter()
            .zip(padded.iter().rev())
            .try_for_each(|(constant, byte)| ac.equal_to_constant(byte.var(), *constant))?;
        let digest_part = hash.to_bytes(ac);
        digest_part
            .iter()
            .zip(padded.iter().rev().skip(self.fixed_part.len()))
            .try_for_each(|(digest_byte, byte)| ac.equal(byte.var(), digest_byte.var()))?;

        Ok(())
    }
}

#[cfg(test)]
#[cfg(any(feature = "arkworks", feature = "halo2"))]
pub(crate) mod test {
    use super::{RsaGadget, KEY_BITS};
    use crate::{
        ir::{
            ac::{AbstractCircuit, AbstractConfig},
            bitwise::BitwiseIRConfig,
        },
        utils::test::xor_rng,
        Field,
    };
    use num_bigint::BigUint;
    use rand::Rng;

    use rsa::signature::SignatureEncoding;
    use rsa::signature::Signer;
    use rsa::{pkcs1v15::SigningKey, traits::PublicKeyParts, RsaPrivateKey};
    use sha2::Sha256;

    pub(crate) fn rsa_test<F: Field>(
        ac: &mut AbstractCircuit<F>,
        rng: &mut impl Rng,
        priv_key: Option<RsaPrivateKey>,
        msg_len: usize,
        limb_size: usize,
        sublimb_size: usize,
    ) {
        let msg: Vec<u8> = (0..msg_len).map(|_| rng.gen()).collect();
        let pub_key = priv_key.as_ref().map(|priv_key| {
            let pub_key = priv_key.to_public_key();
            let pub_key_n = pub_key.n();
            let pub_key_n = pub_key_n.to_bytes_be();
            BigUint::from_bytes_be(&pub_key_n)
        });

        let sig = priv_key.as_ref().map(|priv_key| {
            let sig_key = SigningKey::<Sha256>::new(priv_key.clone());
            let sig = sig_key.sign(&msg[..]);
            let sig = sig.to_bytes();
            BigUint::from_bytes_be(&sig)
        });

        let rsa_gadget =
            RsaGadget::new(ac, limb_size, sublimb_size, pub_key.as_ref().into()).unwrap();
        rsa_gadget
            .verify(ac, &msg.into(), msg_len, sig.as_ref().into())
            .unwrap();
    }

    #[test]
    fn test_rsa() {
        #[cfg(feature = "arkworks")]
        use ark_bn254::Fr;
        #[cfg(feature = "halo2")]
        use halo2_proofs::halo2curves::bn256::Fr;
        use rand_core::OsRng;
        let cfg = AbstractConfig {
            xor: BitwiseIRConfig::Lookup { num_bits: 8 },
            and: BitwiseIRConfig::Lookup { num_bits: 8 },
            sanity: true,
            ..Default::default()
        };
        let ac = &mut AbstractCircuit::<Fr>::new(cfg);
        let rng = &mut xor_rng();
        let priv_key = RsaPrivateKey::new(&mut OsRng, KEY_BITS).unwrap();
        rsa_test::<Fr>(ac, rng, Some(priv_key), 1000, 90, 15);
    }
}
