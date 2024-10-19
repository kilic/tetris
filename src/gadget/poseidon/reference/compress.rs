use super::Permutation;
use crate::Field;

#[derive(Debug)]
/// `Compress` is n-to-1 compression function
pub struct Compress<F: Field, P: Permutation<F>> {
    permutation: P,
    _marker: std::marker::PhantomData<F>,
}

impl<F: Field, P: Permutation<F>> Compress<F, P> {
    pub fn new(permutation: P) -> Self {
        Self {
            permutation,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn compress(&self, input: &[F]) -> F {
        assert_eq!(input.len(), self.permutation.rate());
        let mut state = self.permutation.initial_state();
        self.permutation.permute_with_inputs(&mut state, input);
        state[0]
    }
}
