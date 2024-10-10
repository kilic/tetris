use super::e6::E6;
use crate::{
    gadget::{big_field::VarBig, ecc::Point},
    Error, Field, Value,
};
use num_bigint::BigUint;

pub trait Bw6Pairing {
    fn final_exp_witness(p1: &[Point<BigUint>], p2: &[Point<BigUint>]) -> E6<BigUint>;
    fn double(acc: &mut Point<BigUint>) -> (BigUint, BigUint);
    fn endo(acc: &[Point<BigUint>]) -> Vec<Point<BigUint>>;
    fn add(
        acc: &mut Point<BigUint>,
        p: &Point<BigUint>,
        neg: bool,
        endo: bool,
    ) -> (BigUint, BigUint);
    fn e6_inverse<N: Field>(e: &E6<VarBig<N>>) -> Result<Value<E6<BigUint>>, Error>;
}
