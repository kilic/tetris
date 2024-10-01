pub mod parameters;
pub mod reference;
#[cfg(test)]
pub(crate) mod test;

use crate::{
    ir::{
        ac::AbstractCircuit,
        combination::{linear::Lc, CombinationGadget},
    },
    lc, Field, Var,
};
use reference::{Poseidon, SpongeMode};

#[derive(Clone)]
pub struct PoseidonGadget<F: Field> {
    cfg: Poseidon<F>,
}

impl<F: Field> PoseidonGadget<F> {
    fn sbox_full(&self, ac: &mut AbstractCircuit<F>, state: &mut [Var<F>]) {
        state.iter_mut().for_each(|word| {
            *word = ac.pow5(word);
        });
    }

    fn sbox_part(&self, ac: &mut AbstractCircuit<F>, state: &mut [Var<F>]) {
        state[0] = ac.pow5(&state[0]);
    }

    fn add_inputs(
        &self,
        ac: &mut AbstractCircuit<F>,
        constants: &[F],
        inputs: &[Var<F>],
        state: &mut [Var<F>],
    ) {
        let inputs = std::iter::repeat(None)
            .take(self.cfg.capacity)
            .chain(inputs.iter().map(Some).chain(std::iter::repeat(None)));

        state
            .iter_mut()
            .zip(constants.iter())
            .zip(inputs)
            .for_each(|((word, constant), input)| *word = ac.eval(lc!(*constant) + *word + input));
    }

    fn apply_mds(&self, ac: &mut AbstractCircuit<F>, state: &mut [Var<F>], constants: &[F]) {
        assert!(state.len() == self.cfg.mds.width);
        assert!(constants.len() == self.cfg.mds.width);

        let new_state = self
            .cfg
            .mds
            .rows()
            .zip(constants.iter())
            .map(|(row, constant)| {
                ac.eval(lc!(*constant) + state.iter().zip(row.iter()).map(|(s, e)| s * e))
            })
            .collect::<Vec<_>>();

        state.copy_from_slice(&new_state)
    }

    pub fn permute(
        &mut self,
        ac: &mut AbstractCircuit<F>,
        inputs: &[Var<F>],
        state: &mut [Var<F>],
    ) {
        assert!(inputs.len() <= self.cfg.rate);

        let r_f = self.cfg.r_f / 2;
        let r_p = self.cfg.r_p;

        self.add_inputs(
            ac,
            &self.cfg.constants.first().unwrap().clone(),
            inputs,
            state,
        );
        for constants in self.cfg.constants.iter().skip(1).take(r_f) {
            self.sbox_full(ac, state);
            self.apply_mds(ac, state, constants);
        }

        for constants in self.cfg.constants.iter().skip(1 + r_f).take(r_p) {
            self.sbox_part(ac, state);
            self.apply_mds(ac, state, constants);
        }

        for constants in self.cfg.constants.iter().skip(1 + r_f + r_p).take(r_f - 1) {
            self.sbox_full(ac, state);
            self.apply_mds(ac, state, constants);
        }

        self.sbox_full(ac, state);
        self.apply_mds(ac, state, &vec![F::zero(); self.cfg.width()]);
    }
}

#[derive(Clone)]
pub struct PoseidonSpongeGadget<F: Field> {
    state: Vec<Var<F>>,
    poseidon: PoseidonGadget<F>,
    absorbing: Vec<Var<F>>,
    squeeze_count: Option<usize>,
}

impl<F: Field> PoseidonSpongeGadget<F> {
    pub fn new(ac: &mut AbstractCircuit<F>, cfg: &Poseidon<F>) -> Self {
        let state = cfg
            .initial_state()
            .iter()
            .map(|word| ac.get_constant(*word))
            .collect::<Vec<_>>();

        let poseidon = PoseidonGadget { cfg: cfg.clone() };
        Self {
            state,
            poseidon,
            absorbing: Vec::new(),
            squeeze_count: None,
        }
    }
}

impl<F: Field> PoseidonSpongeGadget<F> {
    fn mode(&self) -> SpongeMode {
        match self.squeeze_count {
            Some(_) => {
                assert!(self.absorbing.is_empty());
                SpongeMode::Squeezing
            }
            None => SpongeMode::Absorbing,
        }
    }

    pub fn absorb(&mut self, input: &[Var<F>]) {
        if input.is_empty() {
            return;
        }
        self.squeeze_count = None;
        self.absorbing.extend(input);
    }

    pub fn squeeze(&mut self, ac: &mut AbstractCircuit<F>, n: usize) -> Vec<Var<F>> {
        if n == 0 {
            return Vec::new();
        }

        let rate = self.poseidon.cfg.rate;
        match self.mode() {
            SpongeMode::Absorbing => {
                // Do absorb inputs
                assert!(!self.absorbing.is_empty());

                // Add inputs and apply a permutation
                self.absorbing
                    .chunks(rate)
                    .for_each(|chunk| self.poseidon.permute(ac, chunk, &mut self.state));
                // Flush the absorbing line
                self.absorbing.clear();
                // Change to the squeezing mode
                self.squeeze_count = Some(0);
            }
            SpongeMode::Squeezing => {
                assert!(self.absorbing.is_empty());
                assert!(self.squeeze_count.is_some());
            }
        }

        let mut output = Vec::new();
        for _ in 0..n {
            let squeeze_count = self.squeeze_count.unwrap();
            let out_index = squeeze_count % rate;

            // apply a permutation when rate number of elements are read
            (out_index == 0 && squeeze_count != 0)
                .then(|| self.poseidon.permute(ac, &[], &mut self.state));

            // skip the capacity elements
            let out_index = out_index + self.poseidon.cfg.capacity;
            output.push(self.state[out_index]);
            if let Some(c) = self.squeeze_count.as_mut() {
                *c += 1;
            }
        }

        output
    }
}
