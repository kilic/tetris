use super::parameters::Grain;
use crate::Field;
use num_traits::Zero;

fn sqrt(aa: usize) -> usize {
    let a = num_integer::sqrt(aa);
    assert_eq!(a * a, aa);
    a
}

#[inline]
fn pow5<F: Field>(e: &mut F) {
    *e *= e.square().square();
}

#[derive(Clone, Debug)]
pub struct Poseidon<F: Field> {
    pub(crate) r_f: usize,
    pub(crate) r_p: usize,
    pub(crate) capacity: usize,
    pub(crate) rate: usize,
    pub(crate) mds: MDS<F>,
    pub(crate) constants: Vec<Vec<F>>,
    pub(crate) initial_state: Option<Vec<F>>,
}

impl<F: Field> Poseidon<F> {
    pub fn generate(
        r_f: usize,
        r_p: usize,
        rate: usize,
        capacity: usize,
        initial_state: Option<Vec<F>>,
    ) -> Self {
        let (constants, mds) = Grain::<F>::generate(r_f, r_p, rate + capacity);
        Self::new(r_f, r_p, capacity, rate, mds, constants, initial_state)
    }

    pub fn new(
        r_f: usize,
        r_p: usize,
        capacity: usize,
        rate: usize,
        mds: MDS<F>,
        constants: Vec<Vec<F>>,
        initial_state: Option<Vec<F>>,
    ) -> Self {
        let width = capacity + rate;
        assert!(mds.width == width);
        assert_eq!(constants.len(), r_f + r_p);
        assert!(constants.iter().all(|c| c.len() == width));
        if let Some(s) = &initial_state {
            assert_eq!(s.len(), width);
        }
        Self {
            r_f,
            r_p,
            capacity,
            rate,
            mds,
            constants,
            initial_state,
        }
    }

    pub(crate) fn width(&self) -> usize {
        self.rate + self.capacity
    }

    pub(crate) fn initial_state(&self) -> Vec<F> {
        self.initial_state
            .clone()
            .unwrap_or_else(|| vec![F::zero(); self.width()])
    }

    fn add_constants(&self, state: &mut [F], round: usize) {
        assert_eq!(state.len(), self.width());

        state
            .iter_mut()
            .zip(self.constants[round].iter())
            .for_each(|(e, constant)| e.add_assign(*constant));
    }

    pub fn permute(&self, state: &mut [F]) {
        assert_eq!(state.len(), self.width());

        let (half_r_f, r_p) = (self.r_f / 2, self.r_p);

        for round in 0..half_r_f {
            self.add_constants(state, round);
            state.iter_mut().for_each(pow5);
            self.mds.apply(state);
        }

        for round in half_r_f..half_r_f + r_p {
            self.add_constants(state, round);
            state.first_mut().map(pow5).unwrap();
            self.mds.apply(state);
        }

        for round in half_r_f + r_p..half_r_f + r_p + half_r_f {
            self.add_constants(state, round);
            state.iter_mut().for_each(pow5);
            self.mds.apply(state);
        }
    }
}

#[derive(Clone, Debug)]
pub struct MDS<F: Field> {
    pub(super) els: Vec<F>,
    pub(super) width: usize,
}

impl<F: Field> MDS<F> {
    pub fn new(els: Vec<F>) -> Self {
        let width = sqrt(els.len());
        assert!(!width.is_zero());
        Self { els, width }
    }

    pub(super) fn rows(&self) -> impl Iterator<Item = &[F]> {
        self.els.chunks(self.width)
    }

    fn apply(&self, state: &mut [F]) {
        assert_eq!(state.len(), self.width);
        let mut result = vec![F::zero(); self.width];
        for (row, cell) in self.rows().zip(result.iter_mut()) {
            row.iter()
                .zip(state.iter())
                .for_each(|(a_i, v_i)| *cell += *v_i * *a_i);
        }
        state.copy_from_slice(&result);
    }
}

#[derive(Clone, Debug)]
pub struct PoseidonSponge<F: Field> {
    cfg: Poseidon<F>,
    state: Vec<F>,
    absorbing: Vec<F>,
    squeeze_count: Option<usize>,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum SpongeMode {
    Absorbing,
    Squeezing,
}

impl<F: Field> PoseidonSponge<F> {
    pub fn new(cfg: &Poseidon<F>) -> Self {
        let state = cfg.initial_state();
        Self {
            cfg: cfg.clone(),
            state,
            absorbing: Vec::new(),
            squeeze_count: None,
        }
    }

    fn mode(&self) -> SpongeMode {
        match self.squeeze_count {
            Some(_) => {
                assert!(self.absorbing.is_empty());
                SpongeMode::Squeezing
            }
            None => SpongeMode::Absorbing,
        }
    }

    pub fn absorb(&mut self, input: &[F]) {
        if input.is_empty() {
            return;
        }
        self.squeeze_count = None;
        self.absorbing.extend_from_slice(input);
    }

    pub fn squeeze(&mut self, n: usize) -> Vec<F> {
        if n == 0 {
            return Vec::new();
        }

        let rate = self.cfg.rate;
        match self.mode() {
            SpongeMode::Absorbing => {
                // Do absorb inputs
                assert!(!self.absorbing.is_empty());

                // Add inputs and apply a permutation
                self.absorbing.chunks(rate).for_each(|chunk| {
                    self.state
                        .iter_mut()
                        .skip(self.cfg.capacity)
                        .zip(chunk.iter())
                        .for_each(|(s, c)| *s += *c);
                    self.cfg.permute(&mut self.state);
                });
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
        (0..n).for_each(|_| {
            let squeeze_count = self.squeeze_count.unwrap();
            let out_index = squeeze_count % rate;

            // apply a permutation when rate number of elements are read
            (out_index == 0 && squeeze_count != 0).then(|| self.cfg.permute(&mut self.state));

            // skip the capacity elements
            let out_index = out_index + self.cfg.capacity;
            output.push(self.state[out_index]);
            if let Some(c) = self.squeeze_count.as_mut() {
                *c += 1;
            }
        });
        output
    }
}
