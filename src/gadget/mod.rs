use crate::{ir::ac::AbstractCircuit, Field, Term, Value, Var};
use itertools::Itertools;
use num_traits::ToPrimitive;

#[cfg(any(feature = "arkworks", feature = "halo2"))]
pub mod big_field;
#[cfg(any(feature = "arkworks", feature = "halo2"))]
pub mod ecc;
#[cfg(any(feature = "arkworks", feature = "halo2"))]
pub mod poseidon;
#[cfg(any(feature = "arkworks", feature = "halo2"))]
pub mod rsa;
#[cfg(any(feature = "arkworks", feature = "halo2"))]
pub mod sha256;

#[derive(Debug, Clone, Copy)]
pub struct VarByte<N: Field>(Var<N>);

impl<N: Field> VarByte<N> {
    pub fn var(&self) -> &Var<N> {
        &self.0
    }

    pub fn assign_many(
        ac: &mut AbstractCircuit<N>,
        bytes: &Value<Vec<u8>>,
        len: usize,
    ) -> Vec<Self> {
        let bytes = bytes
            .as_ref()
            .map(|msg| msg.iter().map(|b| N::from_u64(*b as u64)).collect_vec());
        let bytes = bytes.transpose_vec(len);
        bytes
            .iter()
            .map(|b| VarByte(ac.range_assign(8, b).unwrap()))
            .collect_vec()
    }

    pub fn value(&self) -> Value<u8> {
        self.0.value().map(|v| v.uint().to_u8().unwrap())
    }
}
