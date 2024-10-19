use super::PermutationGadget;
use crate::{ir::ac::AbstractCircuit, Field, Var};

#[derive(Clone)]
pub struct CompressGadget<F: Field, P: PermutationGadget<F>> {
    permutation: P,
    initial_state: Vec<Var<F>>,
}

impl<F: Field, P: PermutationGadget<F>> CompressGadget<F, P> {
    pub fn new(ac: &mut AbstractCircuit<F>, permutation: P) -> Self {
        let initial_state = permutation
            .initial_state()
            .iter()
            .map(|word| ac.get_constant(*word))
            .collect::<Vec<_>>();
        Self {
            permutation,
            initial_state,
        }
    }

    pub fn compress(&self, ac: &mut AbstractCircuit<F>, input: &[Var<F>]) -> Var<F> {
        assert_eq!(input.len(), self.permutation.rate());
        let mut state = self.initial_state.clone();
        self.permutation.permute(ac, &mut state, input);
        state[0]
    }
}
