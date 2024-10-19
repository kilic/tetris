mod compress;
mod grain;
mod poseidon;
mod sponge;

use crate::Field;
pub use compress::Compress;
pub use poseidon::Poseidon;
pub use sponge::Sponge;

pub trait State<F> {
    fn width(&self) -> usize;
    fn rate(&self) -> usize;
    fn cap(&self) -> usize {
        self.width() - self.rate()
    }
    fn initial_state(&self) -> Vec<F>;
}

pub trait Permutation<F>: State<F> {
    fn permute(&self, state: &mut [F])
    where
        F: Field;
    fn add_inputs(&self, state: &mut [F], inputs: &[F])
    where
        F: Field,
    {
        state
            .iter_mut()
            .skip(self.cap())
            .zip(inputs.iter())
            .for_each(|(s, i)| *s += *i);
    }
    fn permute_with_inputs(&self, state: &mut [F], inputs: &[F])
    where
        F: Field,
    {
        self.add_inputs(state, inputs);
        self.permute(state);
    }
}
