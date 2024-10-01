use crate::{
    gadget::{big_field::VarBig, ecc::Point},
    Error, Field, Value,
};
use num_bigint::BigUint;

use super::{e12::E12, e2::E2};

pub trait BNPairing {
    fn w1() -> E12<BigUint>;
    fn w2() -> E12<BigUint>;
    fn e12_inverse<N: Field>(e: &E12<VarBig<N>>) -> Result<Value<E12<BigUint>>, Error>;
    fn final_exp_witness(p1: &[Point<BigUint>], p2: &[Point<E2<BigUint>>])
        -> (E12<BigUint>, usize);
    fn double(acc: &mut Point<E2<BigUint>>) -> (E2<BigUint>, E2<BigUint>);
    fn add(
        acc: &mut Point<E2<BigUint>>,
        p: &Point<E2<BigUint>>,
        neg: bool,
    ) -> (E2<BigUint>, E2<BigUint>);
}
