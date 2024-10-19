pub mod compress;
pub mod reference;
pub mod sponge;

#[cfg(test)]
pub(crate) mod test;

use crate::{
    ir::{
        ac::AbstractCircuit,
        combination::{linear::Lc, CombinationGadget},
    },
    lc, Field, Var,
};
use reference::{Poseidon, State};

pub trait PermutationGadget<F: Field>: State<F> {
    fn permute(&self, ac: &mut AbstractCircuit<F>, state: &mut [Var<F>], inputs: &[Var<F>]);
}

#[derive(Clone)]
pub struct PoseidonGadget<F: Field> {
    cfg: Poseidon<F>,
}

impl<F: Field> State<F> for PoseidonGadget<F> {
    fn width(&self) -> usize {
        self.cfg.width()
    }

    fn rate(&self) -> usize {
        self.cfg.rate()
    }

    fn initial_state(&self) -> Vec<F> {
        self.cfg.initial_state()
    }
}

impl<F: Field> PermutationGadget<F> for PoseidonGadget<F> {
    fn permute(&self, ac: &mut AbstractCircuit<F>, state: &mut [Var<F>], inputs: &[Var<F>]) {
        self.permute(ac, state, inputs);
    }
}

impl<F: Field> PoseidonGadget<F> {
    pub fn new(cfg: Poseidon<F>) -> Self {
        Self { cfg }
    }

    fn sbox_full(&self, ac: &mut AbstractCircuit<F>, state: &mut [Var<F>]) {
        state.iter_mut().for_each(|word| *word = ac.pow5(word));
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

    pub fn permute(&self, ac: &mut AbstractCircuit<F>, state: &mut [Var<F>], inputs: &[Var<F>]) {
        assert!(inputs.len() <= self.cfg.rate);

        let r_f = self.cfg.r_f / 2;
        let r_p = self.cfg.r_p;

        self.add_inputs(
            ac,
            &self.cfg.constants.first().unwrap().clone(),
            inputs,
            state,
        );
        for c in self.cfg.constants.iter().skip(1).take(r_f) {
            self.sbox_full(ac, state);
            self.apply_mds(ac, state, c);
        }
        for c in self.cfg.constants.iter().skip(1 + r_f).take(r_p) {
            self.sbox_part(ac, state);
            self.apply_mds(ac, state, c);
        }
        for c in self.cfg.constants.iter().skip(1 + r_f + r_p).take(r_f - 1) {
            self.sbox_full(ac, state);
            self.apply_mds(ac, state, c);
        }

        self.sbox_full(ac, state);
        self.apply_mds(ac, state, &vec![F::zero(); self.cfg.width()]);
    }
}
