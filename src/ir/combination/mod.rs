use crate::{Error, Field, Value, Var};

pub mod linear;
pub mod quad;

pub trait CombinationIR<F: Field> {
    fn verify(&self) -> Result<(), Error> {
        self.is_zero().maybe(|e| e.then_some(())).map(|_| ())
    }

    fn is_zero(&self) -> Value<bool> {
        self.value().map(|u0| u0 == F::zero())
    }
    fn new(constant: F) -> Self;
    fn is_empty(&self) -> bool;
    fn value(&self) -> Value<F>;
    fn scale(&mut self, factor: F);
    fn add_constant(&mut self, constant: F);
}

pub trait CombinationGadget<F: Field, C: CombinationIR<F>> {
    /// Constaint the combination that evaluates to zero
    fn zero_sum(&mut self, c: C) -> Result<(), Error>;
    /// Evaluate the combination and make it zero sum constrain as `sum(combination) - result = 0` and return the result
    fn eval(&mut self, c: C) -> Var<F>;
}
