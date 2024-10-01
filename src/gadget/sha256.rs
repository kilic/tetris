use crate::ir::combination::CombinationIR;
use crate::utils::decompose_uint;
use crate::{
    ir::{
        ac::AbstractCircuit,
        combination::{quad::Qc, CombinationGadget},
    },
    qc, Field, Var,
};
use itertools::{izip, Itertools};
use num_integer::div_ceil;

use super::VarByte;

const INIT_CONSTANTS: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

const ROUND_CONSTANTS: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

const NUMBER_OF_LIMBS: usize = 4;
const BYTE_SIZE: usize = 8;
const WORD_SIZE: usize = NUMBER_OF_LIMBS * BYTE_SIZE;
const BLOCK_SIZE: usize = 64;

#[derive(Debug, Clone, Copy)]
struct WordInBytes<N: Field>([VarByte<N>; 4]);

impl<N: Field> WordInBytes<N> {
    fn iter(&self) -> impl Iterator<Item = &VarByte<N>> {
        self.0.iter()
    }

    fn bytes(&self) -> &[VarByte<N>] {
        &self.0
    }

    fn vars(&self) -> Vec<Var<N>> {
        self.bytes().iter().map(|b| b.0).collect()
    }
}

#[derive(Debug, Clone, Copy)]
struct Word<N: Field>(Var<N>);

#[derive(Debug, Clone, Copy)]
struct State<N: Field> {
    w: [Word<N>; 8],
    b: [WordInBytes<N>; 8],
}

#[derive(Debug, Clone, Copy)]
pub struct HashInWords<N: Field>([Word<N>; 8]);

#[derive(Debug, Clone, Copy)]
struct Block<N: Field>([Word<N>; 16]);

#[derive(Debug, Clone)]
pub struct Sha256Gadget<N: Field> {
    u_var: [Word<N>; 8],
    u_bytes: [WordInBytes<N>; 8],
    k: [N; 64],
}

impl<N: Field> HashInWords<N> {
    pub fn to_bytes(&self, ac: &mut AbstractCircuit<N>) -> [VarByte<N>; 32] {
        self.0
            .iter()
            .flat_map(|w| limbs(ac, w).0.into_iter().rev().collect_vec())
            .collect_vec()
            .try_into()
            .unwrap()
    }
}

impl<N: Field> Sha256Gadget<N> {
    pub fn new(ac: &mut AbstractCircuit<N>) -> Self {
        let u: [N; 8] = INIT_CONSTANTS
            .iter()
            .map(|&x| N::from_u64(x as u64))
            .collect_vec()
            .try_into()
            .unwrap();
        let u_var: [Word<N>; 8] = u
            .iter()
            .map(|&x| Word(ac.get_constant(x)))
            .collect_vec()
            .try_into()
            .unwrap();
        let u_bytes = u_var
            .iter()
            .map(|&x| limbs(ac, &x))
            .collect_vec()
            .try_into()
            .unwrap();
        let k = ROUND_CONSTANTS
            .iter()
            .map(|&x| N::from_u64(x as u64))
            .collect_vec()
            .try_into()
            .unwrap();

        Self { u_var, u_bytes, k }
    }
}

fn rot<N: Field>(ac: &mut AbstractCircuit<N>, word: &Word<N>, shift: usize) -> WordInBytes<N> {
    let off0 = shift % BYTE_SIZE;
    let mut limbs = if off0 == 0 {
        ac.decompose(BYTE_SIZE, WORD_SIZE, &word.0).unwrap()
    } else {
        let off1 = BYTE_SIZE - off0;
        let sizes = std::iter::once(off0)
            .chain(std::iter::repeat(8).take(NUMBER_OF_LIMBS - 1))
            .chain(std::iter::once(off1))
            .collect::<Vec<_>>();
        let limbs = ac.decompose_nonuniform(&sizes, &word.0).unwrap();
        let merged = {
            let first = limbs.first().unwrap();
            let last = limbs.last().unwrap();
            let base = N::from_u64(1u64 << off1);
            ac.eval(qc!() + first * base + last)
        };
        limbs
            .iter()
            .skip(1)
            .copied()
            .take(NUMBER_OF_LIMBS - 1)
            .chain(std::iter::once(merged))
            .collect::<Vec<_>>()
    };

    limbs.rotate_left(shift / BYTE_SIZE);
    WordInBytes(
        limbs
            .into_iter()
            .map(VarByte)
            .collect_vec()
            .try_into()
            .unwrap(),
    )
}

fn rhs<N: Field>(ac: &mut AbstractCircuit<N>, word: &Word<N>, shift: usize) -> WordInBytes<N> {
    let off0 = shift % BYTE_SIZE;
    let limbs = if off0 == 0 {
        ac.decompose(BYTE_SIZE, WORD_SIZE, &word.0).unwrap()
    } else {
        let off1 = BYTE_SIZE - off0;
        let sizes = std::iter::once(off0)
            .chain(std::iter::repeat(8).take(NUMBER_OF_LIMBS - 1))
            .chain(std::iter::once(off1))
            .collect::<Vec<_>>();
        ac.decompose_nonuniform(&sizes, &word.0).unwrap()
    };

    let zero = VarByte(ac.zero());
    let n_skip = div_ceil(shift, 8);
    WordInBytes(
        limbs
            .into_iter()
            .map(VarByte)
            .skip(n_skip)
            .chain(std::iter::repeat(zero))
            .take(NUMBER_OF_LIMBS)
            .collect_vec()
            .try_into()
            .unwrap(),
    )
}

fn xor3<N: Field>(
    ac: &mut AbstractCircuit<N>,
    w0: &WordInBytes<N>,
    w1: &WordInBytes<N>,
    w2: &WordInBytes<N>,
) -> WordInBytes<N> {
    WordInBytes(
        w0.iter()
            .zip(w1.iter())
            .zip(w2.iter())
            .map(|((l1, l2), l3)| {
                let t = ac.xor_word(&l1.0, &l2.0);
                VarByte(ac.xor_word(&t, &l3.0))
            })
            .collect_vec()
            .try_into()
            .unwrap(),
    )
}

fn xor<N: Field>(
    ac: &mut AbstractCircuit<N>,
    w0: &WordInBytes<N>,
    w1: &WordInBytes<N>,
) -> WordInBytes<N> {
    WordInBytes(
        w0.iter()
            .zip(w1.iter())
            .map(|(l1, l2)| VarByte(ac.xor_word(&l1.0, &l2.0)))
            .collect_vec()
            .try_into()
            .unwrap(),
    )
}

fn and<N: Field>(
    ac: &mut AbstractCircuit<N>,
    w0: &WordInBytes<N>,
    w1: &WordInBytes<N>,
) -> WordInBytes<N> {
    WordInBytes(
        w0.iter()
            .zip(w1.iter())
            .map(|(l1, l2)| VarByte(ac.and_word(&l1.0, &l2.0)))
            .collect_vec()
            .try_into()
            .unwrap(),
    )
}

fn limbs<N: Field>(ac: &mut AbstractCircuit<N>, w: &Word<N>) -> WordInBytes<N> {
    WordInBytes(
        ac.decompose(8, 32, &w.0)
            .unwrap()
            .into_iter()
            .map(VarByte)
            .collect_vec()
            .try_into()
            .unwrap(),
    )
}

fn add<N: Field>(
    ac: &mut AbstractCircuit<N>,
    w0: &[Word<N>],
    w1: &[WordInBytes<N>],
    constant: N,
) -> (Word<N>, WordInBytes<N>) {
    let mut qc = qc!(constant);
    w0.iter().for_each(|w| qc += &w.0);
    w1.iter()
        .for_each(|w| qc += Qc::compose(&w.vars(), BYTE_SIZE));
    let overflow = ac.eval(qc);
    let mut limbs = ac
        .decompose(BYTE_SIZE, WORD_SIZE + BYTE_SIZE, &overflow)
        .unwrap();
    limbs.pop();
    let word = Word(ac.compose(&limbs, BYTE_SIZE));
    let word_in_bytes = WordInBytes(
        limbs
            .into_iter()
            .map(VarByte)
            .collect_vec()
            .try_into()
            .unwrap(),
    );
    (word, word_in_bytes)
}

fn add_overflow<N: Field>(
    ac: &mut AbstractCircuit<N>,
    w0: &[Word<N>],
    w1: &[WordInBytes<N>],
    constant: N,
) -> Word<N> {
    let mut qc = qc!(constant);
    w0.iter().for_each(|w0| qc += &w0.0);
    w1.iter()
        .for_each(|w1| qc += Qc::compose(&w1.vars(), BYTE_SIZE));
    Word(ac.eval(qc))
}

fn ch<N: Field>(
    ac: &mut AbstractCircuit<N>,
    e: &WordInBytes<N>,
    f: &WordInBytes<N>,
    g: &WordInBytes<N>,
) -> WordInBytes<N> {
    let f_xor_g = xor(ac, f, g);
    let e_and_f_xor_g = and(ac, e, &f_xor_g);
    xor(ac, &e_and_f_xor_g, g)
}

fn maj<N: Field>(
    ac: &mut AbstractCircuit<N>,
    a: &WordInBytes<N>,
    b: &WordInBytes<N>,
    c: &WordInBytes<N>,
) -> WordInBytes<N> {
    let t0 = xor(ac, b, c);
    let t1 = and(ac, b, c);
    let t0 = and(ac, a, &t0);
    xor(ac, &t0, &t1)
}

impl<N: Field> Sha256Gadget<N> {
    fn new_state(&self) -> State<N> {
        State {
            w: self.u_var,
            b: self.u_bytes,
        }
    }

    pub fn hash_to_bytes(
        &self,
        ac: &mut AbstractCircuit<N>,
        hash: &HashInWords<N>,
    ) -> [VarByte<N>; 32] {
        hash.0
            .iter()
            .flat_map(|w| limbs(ac, w).0.into_iter().rev().collect_vec())
            .collect_vec()
            .try_into()
            .unwrap()
    }

    pub fn hash(&self, ac: &mut AbstractCircuit<N>, msg: &[VarByte<N>]) -> HashInWords<N> {
        let msg = msg.to_vec();
        let msg_len_in_bytes = msg.len();

        // last 64 bits: len of the original message
        let last_64 = decompose_uint(&(msg.len() * BYTE_SIZE).into(), 8, 8);
        let last_64 = last_64
            .iter()
            .rev()
            .map(|x| VarByte(ac.get_constant(N::from_uint(x).unwrap())))
            .collect_vec();

        let end_byte = VarByte(ac.get_constant(N::from_u64(0x80)));
        let zero = VarByte(ac.get_constant(N::zero()));

        let n_zeros = (BLOCK_SIZE - ((msg_len_in_bytes + BYTE_SIZE + 1) % BLOCK_SIZE)) % BLOCK_SIZE;
        let prepared = msg
            .iter()
            .chain(std::iter::once(&end_byte))
            .chain(std::iter::repeat(&zero).take(n_zeros))
            .chain(&last_64)
            .collect_vec();
        assert_eq!(prepared.len() % 64, 0);

        let mut state = self.new_state();

        prepared.chunks(BLOCK_SIZE).for_each(|block| {
            let block = block
                .chunks(NUMBER_OF_LIMBS)
                .map(|chunk| {
                    let bytes = &chunk.iter().rev().map(|b| b.0).collect_vec();
                    Word(ac.compose(bytes, BYTE_SIZE))
                })
                .collect_vec()
                .try_into()
                .unwrap();
            self.round(ac, &mut state, &Block(block))
        });

        HashInWords(state.w)
    }

    fn round(&self, ac: &mut AbstractCircuit<N>, s: &mut State<N>, block: &Block<N>) {
        let mut w = block.0.to_vec();

        for i in 16..64 {
            let y = &w[i - 15];
            let s00 = &rot(ac, y, 7);
            let s01 = &rot(ac, y, 18);
            let s02 = &rhs(ac, y, 3);
            let s0 = xor3(ac, s00, s01, s02);

            let y = &w[i - 2];
            let s10 = &rot(ac, y, 17);
            let s11 = &rot(ac, y, 19);
            let s12 = &rhs(ac, y, 10);
            let s1 = xor3(ac, s10, s11, s12);

            let (wi, _) = add(ac, &[w[i - 16], w[i - 7]], &[s0, s1], N::zero());
            w.push(wi);
        }

        let mut a = s.w[0];
        let mut a_bytes = s.b[0];
        let mut b = s.b[1];
        let mut c = s.b[2];
        let mut d = s.b[3];
        let mut e = s.w[4];
        let mut e_bytes = s.b[4];
        let mut f = s.b[5];
        let mut g = s.b[6];
        let mut h = s.b[7];

        for (w, k) in izip!(w, self.k) {
            let s10 = &rot(ac, &e, 6);
            let s11 = &rot(ac, &e, 11);
            let s12 = &rot(ac, &e, 25);
            let s1 = xor3(ac, s10, s11, s12);

            let ch = ch(ac, &e_bytes, &f, &g);

            let t1 = add_overflow(ac, &[w], &[h, s1, ch], k);

            let s00 = &rot(ac, &a, 2);
            let s01 = &rot(ac, &a, 13);
            let s02 = &rot(ac, &a, 22);
            let s0 = xor3(ac, s00, s01, s02);
            let maj = maj(ac, &a_bytes, &b, &c);

            h = g;
            g = f;
            f = e_bytes;
            (e, e_bytes) = add(ac, &[t1], &[d], N::zero());

            d = c;
            c = b;
            b = a_bytes;
            (a, a_bytes) = add(ac, &[t1], &[s0, maj], N::zero());
        }

        (s.w[0], s.b[0]) = add(ac, &[s.w[0], a], &[], N::zero());
        (s.w[1], s.b[1]) = add(ac, &[s.w[1]], &[b], N::zero());
        (s.w[2], s.b[2]) = add(ac, &[s.w[2]], &[c], N::zero());
        (s.w[3], s.b[3]) = add(ac, &[s.w[3]], &[d], N::zero());
        (s.w[4], s.b[4]) = add(ac, &[s.w[4], e], &[], N::zero());
        (s.w[5], s.b[5]) = add(ac, &[s.w[5]], &[f], N::zero());
        (s.w[6], s.b[6]) = add(ac, &[s.w[6]], &[g], N::zero());
        (s.w[7], s.b[7]) = add(ac, &[s.w[7]], &[h], N::zero());
    }
}

#[cfg(test)]
#[cfg(any(feature = "arkworks", feature = "halo2"))]

mod test {
    use super::{Sha256Gadget, VarByte};
    use crate::ir::bitwise::BitwiseIRConfig;
    use crate::witness::field::Field;
    use crate::witness::Term;
    use crate::{
        ir::ac::{AbstractCircuit, AbstractConfig},
        utils::test::xor_rng,
    };

    #[cfg(feature = "arkworks")]
    use ark_bn254::Fr;
    #[cfg(feature = "halo2")]
    use halo2_proofs::halo2curves::bn256::Fr;
    use num_traits::ToPrimitive;
    use rand::Rng;

    #[test]
    fn test_rot() {
        fn rotate(value: u64, shift: usize) -> u64 {
            ((value >> shift) | (value << (32 - shift))) & 0xFFFFFFFF
        }
        let cfg = AbstractConfig::default();
        let ac = &mut AbstractCircuit::<Fr>::new(cfg);
        for shift in 0..31 {
            let e = 0x1a2b3c4du64;
            let e_rot = rotate(e, shift);

            let e = Fr::from(e);
            let e_rot = Fr::from(e_rot);
            let e = ac.get_constant(e);
            let e_rot0 = ac.get_constant(e_rot);
            let word = super::rot(ac, &super::Word(e), shift);
            let e_rot1 = ac.compose(&word.vars(), 8);
            ac.equal(&e_rot0, &e_rot1).unwrap();
        }
    }

    #[test]
    fn test_rhs() {
        let cfg = AbstractConfig::default();
        let ac = &mut AbstractCircuit::<Fr>::new(cfg);
        for shift in 0..31 {
            let e = 0x1a2b3c4du64;
            let e_rot = e >> shift;
            let e = Fr::from(e);
            let e_rot = Fr::from(e_rot);
            let e = ac.get_constant(e);
            let e_rot0 = ac.get_constant(e_rot);
            let word = super::rhs(ac, &super::Word(e), shift);
            let e_rot1 = ac.compose(&word.vars(), 8);
            ac.equal(&e_rot0, &e_rot1).unwrap();
        }
    }

    #[test]
    fn test_sha256() {
        let cfg = AbstractConfig {
            xor: BitwiseIRConfig::Lookup { num_bits: 8 },
            and: BitwiseIRConfig::Lookup { num_bits: 8 },
            sanity: false,
            ..Default::default()
        };
        let ac = &mut AbstractCircuit::<Fr>::new(cfg);
        let sha256 = Sha256Gadget::new(ac);

        let rng = &mut xor_rng();
        for msg_len in 0..150 {
            let msg: Vec<u8> = (0..msg_len).map(|_| rng.gen()).collect();
            let expect = {
                use digest::Digest;
                sha2::Sha256::digest(&msg)
            };
            let msg = VarByte::assign_many(ac, &msg.into(), msg_len);
            let hash = sha256.hash(ac, &msg);
            let hash = hash.to_bytes(ac);
            expect.into_iter().zip(hash).for_each(|(b0, b1)| {
                b1.0.value()
                    .map(|b1| assert_eq!(b0, b1.uint().to_u8().unwrap()));
            });
        }
    }
}
