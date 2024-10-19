use super::Permutation;
use crate::Field;

#[derive(Debug)]
/// `Sponge` is proof stream hasher
pub struct Sponge<F: Field, P: Permutation<F>> {
    permutation: P,
    state: Vec<F>,
    input: Vec<F>,
    output: Vec<F>,
}

impl<F: Field, P: Permutation<F>> Sponge<F, P> {
    pub fn new(permutation: P) -> Self {
        let state = permutation.initial_state();
        Self {
            permutation,
            state,
            input: Vec::new(),
            output: Vec::new(),
        }
    }

    pub fn absorb(&mut self, input: &[F]) {
        (!input.is_empty()).then(|| {
            self.output.clear();

            input.iter().for_each(|&input| {
                self.input.push(input);
                (self.input.len() == self.permutation.rate()).then(|| self.permute());
            });
        });
    }

    pub fn squeeze(&mut self, n: usize) -> Vec<F> {
        (0..n)
            .map(|_| {
                (!self.input.is_empty()).then(|| self.permute());
                self.output.is_empty().then(|| self.permute());
                self.output.pop().unwrap()
            })
            .collect()
    }

    fn permute(&mut self) {
        assert!(self.input.len() <= self.permutation.rate());
        let cap = self.permutation.cap();

        // move input buffer to state and apply permutation
        self.permutation
            .permute_with_inputs(&mut self.state, &self.input);
        self.input.clear();

        // refresh output buffer with new state
        self.output.clear();
        self.output.extend(&self.state[cap..]);
    }
}
