use super::{grain::Grain, Permutation, State};
use crate::{utils::sqrt_strict, Field};
use num_traits::Zero;

#[inline]
fn pow5<F: Field>(e: &mut F) {
    *e *= e.square().square();
}

#[derive(Clone, Debug)]
pub struct Mds<F: Field> {
    pub(crate) els: Vec<F>,
    pub(crate) width: usize,
}

impl<F: Field> Mds<F> {
    pub fn new(els: Vec<F>) -> Self {
        let width = sqrt_strict(els.len());
        assert!(!width.is_zero());
        Self { els, width }
    }

    pub(crate) fn rows(&self) -> impl Iterator<Item = &[F]> {
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

    pub(crate) fn cauchy(xs: &[F], ys: &[F]) -> Self {
        let t = xs.len();
        assert!(xs.len() == ys.len());
        let mut m = vec![F::zero(); t * t];

        for (i, x) in xs.iter().enumerate() {
            for (j, y) in ys.iter().enumerate() {
                let sum = *x + *y;
                assert!(!sum.is_zero());
                m[i * t + j] = sum.inv().unwrap();
            }
        }
        Mds::new(m)
    }
}

#[derive(Clone, Debug)]
pub struct Poseidon<F: Field> {
    pub(crate) r_f: usize,
    pub(crate) r_p: usize,
    pub(crate) capacity: usize,
    pub(crate) rate: usize,
    pub(crate) mds: Mds<F>,
    pub(crate) constants: Vec<Vec<F>>,
    pub(crate) initial_state: Option<Vec<F>>,
}

impl<F: Field> State<F> for Poseidon<F> {
    fn rate(&self) -> usize {
        self.rate
    }

    fn width(&self) -> usize {
        self.rate + self.capacity
    }

    fn initial_state(&self) -> Vec<F> {
        self.initial_state
            .clone()
            .unwrap_or_else(|| vec![F::zero(); self.width()])
    }
}

impl<F: Field> Permutation<F> for Poseidon<F> {
    fn permute(&self, state: &mut [F]) {
        let add_constants = |state: &mut [F], round: usize| {
            assert_eq!(state.len(), self.width());
            state
                .iter_mut()
                .zip(self.constants[round].iter())
                .for_each(|(e, constant)| e.add_assign(*constant));
        };

        assert_eq!(state.len(), self.width());
        let (half_r_f, r_p) = (self.r_f / 2, self.r_p);

        for round in 0..half_r_f {
            add_constants(state, round);
            state.iter_mut().for_each(pow5);
            self.mds.apply(state);
        }

        for round in half_r_f..half_r_f + r_p {
            add_constants(state, round);
            state.first_mut().map(pow5).unwrap();
            self.mds.apply(state);
        }

        for round in half_r_f + r_p..half_r_f + r_p + half_r_f {
            add_constants(state, round);
            state.iter_mut().for_each(pow5);
            self.mds.apply(state);
        }
    }
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

        if let Some(initial_state) = &initial_state {
            assert_eq!(initial_state.len(), rate + capacity);
        }

        Self::new(r_f, r_p, capacity, rate, mds, constants, initial_state)
    }

    pub fn new(
        r_f: usize,
        r_p: usize,
        capacity: usize,
        rate: usize,
        mds: Mds<F>,
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
}

#[cfg(test)]
#[cfg(any(feature = "arkworks", feature = "halo2"))]
mod test {
    use super::Poseidon;
    use crate::{gadget::poseidon::reference::Permutation, Field};
    use num_bigint::BigUint;
    use num_traits::Num;

    #[test]
    #[cfg(feature = "arkworks")]
    fn test_parameters_cross() {
        type F = ark_bn254::Fr;
        use ark_crypto_primitives::sponge::poseidon::find_poseidon_ark_and_mds;
        use ark_ff::PrimeField;

        let rate = 2;
        let r_f = 8;
        let r_p = 55;

        let (constants, mds) =
            find_poseidon_ark_and_mds::<F>(F::MODULUS_BIT_SIZE as u64, rate, r_f, r_p, 0);
        let local = Poseidon::<F>::generate(r_f as usize, r_p as usize, rate, 1, None);
        assert_eq!(local.constants, constants);
        assert_eq!(
            local.mds.els,
            mds.iter().flatten().cloned().collect::<Vec<F>>()
        );
    }

    #[test]
    fn test_vectors() {
        #[cfg(feature = "arkworks")]
        type F = ark_bn254::Fr;
        #[cfg(feature = "halo2")]
        type F = halo2_proofs::halo2curves::bn256::Fr;

        use num_bigint::BigUint;
        use num_traits::Num;

        // https://extgit.iaik.tugraz.at/krypto/hadeshash/-/blob/master/code/test_vectors.txt
        // poseidonperm_x5_254_3
        {
            const R_F: usize = 8;
            const R_P: usize = 57;
            const RATE: usize = 2;

            let mut state = vec![0u64, 1, 2]
                .into_iter()
                .map(F::from_u64)
                .collect::<Vec<F>>();
            let poseidon: Poseidon<F> = Poseidon::generate(R_F, R_P, RATE, 1, None);

            poseidon.permute(&mut state);

            let expected = [
                "7853200120776062878684798364095072458815029376092732009249414926327459813530",
                "7142104613055408817911962100316808866448378443474503659992478482890339429929",
                "6549537674122432311777789598043107870002137484850126429160507761192163713804",
            ];
            let expected = expected
                .iter()
                .map(|e| BigUint::from_str_radix(e, 10).unwrap());
            state
                .into_iter()
                .zip(expected)
                .for_each(|(word, expected)| assert_eq!(word.uint(), expected));
        }

        // https://extgit.iaik.tugraz.at/krypto/hadeshash/-/blob/master/code/test_vectors.txt
        // poseidonperm_x5_254_5
        {
            const R_F: usize = 8;
            const R_P: usize = 60;
            const RATE: usize = 4;

            let mut state = vec![0u64, 1, 2, 3, 4]
                .into_iter()
                .map(F::from_u64)
                .collect::<Vec<F>>();
            let poseidon: Poseidon<F> = Poseidon::generate(R_F, R_P, RATE, 1, None);

            poseidon.permute(&mut state);

            let expected = [
                "18821383157269793795438455681495246036402687001665670618754263018637548127333",
                "7817711165059374331357136443537800893307845083525445872661165200086166013245",
                "16733335996448830230979566039396561240864200624113062088822991822580465420551",
                "6644334865470350789317807668685953492649391266180911382577082600917830417726",
                "3372108894677221197912083238087960099443657816445944159266857514496320565191",
            ];
            let expected = expected
                .iter()
                .map(|e| BigUint::from_str_radix(e, 10).unwrap());
            state
                .into_iter()
                .zip(expected)
                .for_each(|(word, expected)| assert_eq!(word.uint(), expected));
        }
    }

    fn circom_rp(rate: usize) -> usize {
        [
            56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68,
        ]
        .get(rate - 1)
        .cloned()
        .unwrap()
    }

    #[test]
    fn test_circom_compat() {
        #[cfg(feature = "arkworks")]
        type F = ark_bn254::Fr;
        #[cfg(feature = "halo2")]
        type F = halo2_proofs::halo2curves::bn256::Fr;

        let expect_decimal = |s: &str, e0: F| {
            let n = BigUint::from_str_radix(s, 10).unwrap();
            let e1 = F::from_uint(&n).unwrap();
            assert_eq!(e0, e1);
        };

        let r_f = 8;
        let cap = 1;

        {
            // https://github.com/iden3/circomlib/blob/0a045aec50d51396fcd86a568981a5a0afb99e95/test/poseidoncircuit.js#L29
            // and
            // https://github.com/iden3/circomlibjs/blob/bfa4ce13661e747e82ed74d1114659e354c1b60b/test/poseidon.js#L130
            let rate = 5;
            let r_p = circom_rp(rate);
            let poseidon: Poseidon<F> = Poseidon::generate(r_f, r_p, rate, cap, None);
            let inputs: Vec<F> = vec![
                0u64.into(),
                1u64.into(),
                2u64.into(),
                0u64.into(),
                0u64.into(),
                0u64.into(),
            ];
            let mut output = inputs.clone();
            poseidon.permute(&mut output);
            expect_decimal(
                "1018317224307729531995786483840663576608797660851238720571059489595066344487",
                output[0],
            );
        }
        {
            // https://github.com/iden3/circomlib/blob/0a045aec50d51396fcd86a568981a5a0afb99e95/test/poseidoncircuit.js#L39
            let rate = 5;
            let r_p = circom_rp(rate);
            let poseidon: Poseidon<F> = Poseidon::generate(r_f, r_p, rate, cap, None);
            let inputs: Vec<F> = vec![
                0u64.into(),
                3u64.into(),
                4u64.into(),
                5u64.into(),
                10u64.into(),
                23u64.into(),
            ];
            let mut output = inputs.clone();
            poseidon.permute(&mut output);
            expect_decimal(
                "13034429309846638789535561449942021891039729847501137143363028890275222221409",
                output[0],
            );
        }
        {
            // https://github.com/iden3/circomlib/blob/0a045aec50d51396fcd86a568981a5a0afb99e95/test/poseidoncircuit.js#L39
            let rate = 2;
            let r_p = circom_rp(rate);
            let poseidon: Poseidon<F> = Poseidon::generate(r_f, r_p, rate, cap, None);
            let inputs: Vec<F> = vec![0u64.into(), 3u64.into(), 4u64.into()];
            let mut output = inputs.clone();
            poseidon.permute(&mut output);
            expect_decimal(
                "14763215145315200506921711489642608356394854266165572616578112107564877678998",
                output[0],
            );
        }

        {
            // https://github.com/iden3/circomlibjs/blob/bfa4ce13661e747e82ed74d1114659e354c1b60b/test/poseidon.js#L53
            let rate = 16;
            let r_p = circom_rp(rate);
            let poseidon: Poseidon<F> = Poseidon::generate(r_f, r_p, rate, cap, None);
            let mut inputs: Vec<F> = vec![
                0u64.into(),
                1u64.into(),
                2u64.into(),
                3u64.into(),
                4u64.into(),
                5u64.into(),
                6u64.into(),
                7u64.into(),
                8u64.into(),
                9u64.into(),
                10u64.into(),
                11u64.into(),
                12u64.into(),
                13u64.into(),
                14u64.into(),
                15u64.into(),
                16u64.into(),
            ];
            let mut output = inputs.clone();
            poseidon.permute(&mut output);
            expect_decimal(
                "9989051620750914585850546081941653841776809718687451684622678807385399211877",
                output[0],
            );

            // https://github.com/iden3/circomlibjs/blob/bfa4ce13661e747e82ed74d1114659e354c1b60b/test/poseidon.js#L93
            inputs[0] = 17u64.into();
            let mut output = inputs.clone();
            poseidon.permute(&mut output);
            expect_decimal(
                "7865037705064445207187340054656830232157001572238023180016026650118519857086",
                output[0],
            );

            let inputs: Vec<F> = vec![
                0u64.into(),
                1u64.into(),
                2u64.into(),
                3u64.into(),
                4u64.into(),
                5u64.into(),
                6u64.into(),
                7u64.into(),
                8u64.into(),
                9u64.into(),
                0u64.into(),
                0u64.into(),
                0u64.into(),
                0u64.into(),
                0u64.into(),
                0u64.into(),
                0u64.into(),
            ];
            let mut output = inputs.clone();
            poseidon.permute(&mut output);
            expect_decimal(
                "11882816200654282475720830292386643970958445617880627439994635298904836126497",
                output[0],
            );
        }

        {
            // https://github.com/iden3/circomlibjs/blob/bfa4ce13661e747e82ed74d1114659e354c1b60b/test/poseidon.js#L85
            let rate = 4;
            let r_p = circom_rp(rate);
            let poseidon: Poseidon<F> = Poseidon::generate(r_f, r_p, rate, cap, None);
            let inputs: Vec<F> = vec![
                7u64.into(),
                1u64.into(),
                2u64.into(),
                3u64.into(),
                4u64.into(),
            ];
            let mut output = inputs.clone();
            poseidon.permute(&mut output);
            expect_decimal(
                "1569211601569591254857354699102545060324851338714426496554851741114291465006",
                output[0],
            );
        }
    }
}
