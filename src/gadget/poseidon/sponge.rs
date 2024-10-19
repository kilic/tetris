use super::PermutationGadget;
use crate::{ir::ac::AbstractCircuit, Field, Var};

#[derive(Clone)]
pub struct SpongeGadget<F: Field, P: PermutationGadget<F>> {
    permutation: P,
    state: Vec<Var<F>>,
    input: Vec<Var<F>>,
    output: Vec<Var<F>>,
}

impl<F: Field, P: PermutationGadget<F>> SpongeGadget<F, P> {
    pub fn new(ac: &mut AbstractCircuit<F>, permutation: P) -> Self {
        let state = permutation
            .initial_state()
            .iter()
            .map(|word| ac.get_constant(*word))
            .collect::<Vec<_>>();

        Self {
            permutation,
            state,
            input: Vec::new(),
            output: Vec::new(),
        }
    }

    pub fn permute(&mut self, ac: &mut AbstractCircuit<F>) {
        assert!(self.input.len() <= self.permutation.rate());

        // apply permutation and move input buffer to state
        self.permutation.permute(ac, &mut self.state, &self.input);
        self.input.clear();

        // refresh output buffer with new state
        self.output.clear();
        self.output
            .extend(&self.state[self.permutation.width() - self.permutation.rate()..]);
    }

    pub fn absorb(&mut self, ac: &mut AbstractCircuit<F>, input: &[Var<F>]) {
        (!input.is_empty()).then(|| {
            self.output.clear();

            input.iter().for_each(|&input| {
                self.input.push(input);
                (self.input.len() == self.permutation.rate()).then(|| self.permute(ac));
            });
        });
    }

    pub fn squeeze(&mut self, ac: &mut AbstractCircuit<F>, n: usize) -> Vec<Var<F>> {
        (0..n)
            .map(|_| {
                (!self.input.is_empty()).then(|| self.permute(ac));
                self.output.is_empty().then(|| self.permute(ac));
                self.output.pop().unwrap()
            })
            .collect()
    }
}
