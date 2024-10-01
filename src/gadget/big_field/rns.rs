use super::num::{Big, VarBig};
use super::{Num, VarNum};
use crate::gadget::VarByte;
use crate::ir::ac::AbstractCircuit;
use crate::ir::combination::quad::Qc;
use crate::ir::combination::CombinationGadget;
use crate::utils::{compose_int, decompose_int, product};
use crate::{qc, QuadScaled, Scaled, Var};
use crate::{utils::compose_uint, witness::field::Field, Error, Value};
use itertools::{izip, Itertools};
use num_bigint::{BigInt, BigUint, ToBigInt};
use num_integer::div_ceil;
use num_integer::Integer as _;
use num_traits::Signed;
use num_traits::{One, Zero};

#[derive(Debug, Clone)]
pub(crate) struct DivModResult {
    pub(crate) q: Value<BigInt>,
    pub(crate) r: Value<BigUint>,
}

impl DivModResult {
    pub(crate) fn q(&self) -> Value<&BigInt> {
        self.q.as_ref()
    }

    pub(crate) fn r(&self) -> Value<&BigUint> {
        self.r.as_ref()
    }
}

#[derive(Debug, Clone)]
pub enum Range {
    Remainder,
    Quotient,
    Overflow(Vec<BigUint>),
}

impl<I> From<I> for Range
where
    I: IntoIterator,
    I::Item: std::borrow::Borrow<BigUint>,
{
    fn from(v: I) -> Self {
        use std::borrow::Borrow;
        Range::Overflow(v.into_iter().map(|e| e.borrow().clone()).collect())
    }
}

pub(crate) fn to_field(e: &BigInt, p: &BigInt) -> BigInt {
    let e = e.mod_floor(p);
    if e.is_negative() {
        e + p
    } else {
        e
    }
}

#[derive(Debug, Clone)]
pub struct Rns<N: Field> {
    pub n_limbs: usize,
    pub limb_size: usize,
    pub mod_size: usize,
    pub sublimb_size: usize,
    pub(crate) n_carries: usize,

    pub(crate) native_mod: BigUint,
    pub(crate) bases: Vec<N>,
    pub(crate) rsh: N,

    #[allow(dead_code)]
    pub(crate) max_unred: BigUint,
    pub(crate) max_rem: BigUint,
    pub(crate) max_op: BigUint,
    pub(crate) max_red_quot: BigUint,
    pub(crate) max_quot: BigUint,

    #[allow(dead_code)]
    pub(crate) max_unred_limbs: Vec<BigUint>,
    pub(crate) max_rem_limbs: Vec<BigUint>,
    pub(crate) max_quot_limbs: Vec<BigUint>,

    p_mul_q_max: Vec<Vec<BigUint>>,
    p_red_q_max: Vec<BigUint>,
}

impl<N: Field> Rns<N> {
    #[allow(dead_code)]
    pub(crate) fn validate_big(&self, big: &Big<N>) -> Result<(), Error> {
        big.validate(self.limb_size)
    }

    pub(crate) fn validate_varbig(&self, big: &VarBig<N>) -> Result<(), Error> {
        big.validate(self.limb_size)
    }

    pub(crate) fn limb_size(&self) -> usize {
        self.limb_size
    }

    pub(crate) fn n_limbs(&self) -> usize {
        self.n_limbs
    }

    pub(crate) fn lsh(&self) -> &N {
        &self.bases[1]
    }

    #[allow(dead_code)]
    pub(crate) fn number_of_bytes(&self) -> usize {
        div_ceil(self.mod_size, 8)
    }

    #[allow(dead_code)]
    pub(crate) fn native_mod(&self) -> &BigUint {
        &self.native_mod
    }

    #[allow(dead_code)]
    pub(crate) fn rsh(&self) -> &N {
        &self.rsh
    }

    #[allow(dead_code)]
    pub(crate) fn big_from_limbs(&self, e: &[BigInt]) -> Big<N> {
        Big::from_limbs(e, self.limb_size)
    }

    #[allow(dead_code)]
    pub(crate) fn big_from_int(&self, e: &BigInt) -> Big<N> {
        Big::new(e, self.n_limbs, self.limb_size)
    }

    pub(crate) fn big_from_uint(&self, e: &BigUint) -> Big<N> {
        Big::new(&e.clone().into(), self.n_limbs, self.limb_size)
    }

    pub(crate) fn limb_sizes(&self, range: &Range) -> Vec<usize> {
        self.max_limbs(range)
            .into_iter()
            .map(|e| e.bits() as usize)
            .collect_vec()
    }

    pub(crate) fn max_value(&self, range: &Range) -> BigUint {
        match range {
            Range::Remainder => self.max_rem.clone(),
            Range::Overflow(max_limbs) => compose_uint(max_limbs, self.limb_size),
            Range::Quotient => self.max_quot.clone(),
        }
    }

    pub(crate) fn max_limbs(&self, range: &Range) -> Vec<BigUint> {
        match range {
            Range::Remainder => self.max_rem_limbs.clone(),
            Range::Overflow(max_limbs) => max_limbs.clone(),
            Range::Quotient => self.max_quot_limbs.clone(),
        }
    }

    pub(crate) fn max_limb_sizes(&self, range: &Range) -> Vec<usize> {
        self.max_limbs(range)
            .into_iter()
            .map(|e| e.bits() as usize)
            .collect_vec()
    }

    pub(crate) fn red_max_carries(&self, w0: &[BigUint]) -> Vec<usize> {
        let mut max_carry = BigUint::zero();
        w0.iter()
            .zip(self.p_red_q_max.iter())
            .take(self.n_carries)
            .map(|(limb, pq)| {
                let t = pq + limb + &max_carry;
                max_carry = t >> self.limb_size;
                max_carry.bits() as usize
            })
            .collect()
    }

    pub fn into_bytes(&self, ac: &mut AbstractCircuit<N>, w: &VarBig<N>) -> Vec<VarByte<N>> {
        let limb_sizes = self.max_limb_sizes(&Range::Remainder);
        let mut pre_off: usize = 0;
        let mut bytes: Vec<Var<_>> = vec![];
        for (limb, limb_size) in w.limbs().zip(limb_sizes) {
            let inter_size = limb_size - pre_off;
            let n_bytes = inter_size / 8;
            let post_off = inter_size - n_bytes * 8;
            let sizes = std::iter::once(pre_off)
                .chain(std::iter::repeat(8).take(n_bytes))
                .chain(std::iter::once(post_off))
                .filter(|&x| x != 0)
                .collect::<Vec<_>>();
            let mut t = ac.decompose_nonuniform(&sizes, limb.var()).unwrap();
            if pre_off != 0 {
                let merged = {
                    let b0 = bytes.pop().unwrap();
                    let b1 = t.first().unwrap();
                    let base = N::from_u64(1u64 << (8 - pre_off));
                    ac.eval(qc!() + b0 + b1 * base)
                };
                t[0] = merged;
            }
            bytes.extend(t.into_iter());
            pre_off = (8 - post_off) % 8;
        }
        let n_bytes = div_ceil(self.mod_size, 8);
        assert_eq!(bytes.len(), n_bytes);
        bytes.into_iter().map(VarByte).collect()
    }

    pub(crate) fn mul_max_carries(
        &self,
        w0: &[BigUint],
        w1: &[BigUint],
        d: Option<&[BigUint]>,
        to_add: &[Vec<BigUint>],
    ) -> Vec<usize> {
        assert_eq!(w0.len(), self.n_limbs);
        assert_eq!(w1.len(), self.n_limbs);
        let mut max_carry = BigUint::zero();

        let ww = product::<BigUint, _, _>(w0, w1);
        let one = &std::iter::once(BigUint::one())
            .chain(std::iter::repeat(BigUint::zero()))
            .take(self.n_limbs)
            .collect_vec()[..];
        let d = d.unwrap_or(one);
        let rd = product::<BigUint, _, _>(d, &self.max_rem_limbs);

        let to_add = (0..self.n_carries).map(|i| {
            to_add
                .iter()
                .map(|e| e.get(i).cloned().unwrap_or(BigUint::zero()))
                .collect_vec()
        });

        ww.iter()
            .zip(rd)
            .zip(self.p_mul_q_max.iter())
            .zip(to_add)
            .take(self.n_carries)
            .map(|(((ww, rd), pq), to_add)| {
                let t = ww
                    .iter()
                    .chain(&rd)
                    .chain(pq)
                    .chain(to_add.iter())
                    .chain(std::iter::once(&max_carry))
                    .sum::<BigUint>();
                assert!(t < self.native_mod, "wraps");
                max_carry = t >> self.limb_size;
                max_carry.bits() as usize
            })
            .collect()
    }

    pub(crate) fn witgen_red(&self, w: Value<&BigInt>, p: Value<&BigInt>) -> DivModResult {
        let (q, r) = w.zip(p).map(|(w, p)| w.div_mod_floor(p)).unzip();
        q.as_ref()
            .map(|q| assert!(q.magnitude() < &self.max_red_quot));
        let r = r.map(|r| r.to_biguint().unwrap());
        DivModResult { q, r }
    }

    pub(crate) fn witgen_mul(
        &self,
        w0: Value<&BigInt>,
        w1: Value<&BigInt>,
        d: Value<&BigInt>,
        to_add: &[Value<BigInt>],
        p: Value<&BigInt>,
    ) -> DivModResult {
        let to_add: Value<Vec<_>> = Value::from_iter(to_add.to_vec());
        let to_add = to_add.map(|to_add| to_add.iter().sum::<BigInt>());
        let (q, r) = w0
            .zip(w1)
            .zip(d)
            .zip(to_add.as_ref())
            .zip(p)
            .map(|((((w0, w1), d), to_add), p)| {
                let d_inv = &d.modinv(p).unwrap();
                let r = (w0 * w1 + to_add) * d_inv;
                let r = to_field(&r, p);
                let wide = w0 * w1 - d * &r + to_add;
                let (q, zero) = wide.div_mod_floor(p);
                assert!(zero.is_zero());
                (q, r.to_biguint().unwrap())
            })
            .unzip();
        q.as_ref().map(|q| assert!(q.magnitude() <= &self.max_quot));
        r.as_ref().map(|r| assert!(r <= &self.max_rem));
        DivModResult { q, r }
    }

    pub(crate) fn construct(mod_size: usize, limb_size: usize, sublimb_size: usize) -> Self {
        let one = &BigUint::one();

        let native_mod = N::modulus();
        let n_limbs = div_ceil(mod_size, limb_size);

        let max_rem = (one << mod_size) - 1usize;
        let pseudo_wrong_mod = &max_rem.clone();
        let pre_binary_mod = (&max_rem * &max_rem) / &native_mod;
        let pre_binary_mod_size = pre_binary_mod.bits() as usize;
        let mut n_carries = div_ceil(pre_binary_mod_size, limb_size);

        println!(
            "RNS construction, limb_size: {limb_size}, n_limbs: {n_limbs}, n_carries {n_carries}"
        );

        let (n_carries, binary_mod, crt_mod, max_quot, max_op) = (0..2)
            .find_map(|_| {
                let binary_mod_size = n_carries * limb_size;
                let binary_mod = one << binary_mod_size;
                let crt_mod = &binary_mod * &native_mod;

                // find max quotient
                // first value is not power of two minus one
                let pre_max_quot = (&crt_mod - &max_rem) / pseudo_wrong_mod;
                // so lets floor it to there
                let mut max_quot = (one << (pre_max_quot.bits() - 1)) - 1usize;

                // if max quotient too large
                // try with one less limb
                let n_quot_limbs = div_ceil(max_quot.bits() as usize, limb_size);
                if n_quot_limbs > n_limbs {
                    max_quot = (one << (n_limbs * limb_size)) - 1usize;
                }

                // `op * op < q * w + r`
                let tt = &max_quot * pseudo_wrong_mod + &max_rem;
                let pre_max_op = tt.sqrt();
                let max_op = (one << (pre_max_op.bits() - 1)) - 1usize;

                if &max_quot < pseudo_wrong_mod {
                    println!("q < w; go second try");
                    n_carries += 1;
                    return None;
                }
                if &max_op < pseudo_wrong_mod {
                    println!("op < w; go second try");
                    n_carries += 1;
                    return None;
                }

                Some((n_carries, binary_mod, crt_mod, max_quot, max_op))
            })
            .unwrap();

        {
            let lhs = &max_op * &max_op;
            let rsh = &max_quot * pseudo_wrong_mod + &max_rem;
            assert!(lhs < rsh);
            assert!(crt_mod > rsh);
            assert!(&binary_mod > pseudo_wrong_mod);
            assert!(binary_mod > native_mod);
            assert!(&max_rem == pseudo_wrong_mod);
            assert!(&max_quot > pseudo_wrong_mod);
            assert!(&max_op > pseudo_wrong_mod);
            assert!(max_rem < binary_mod);
            assert!(max_op < binary_mod);
            assert!(max_quot < binary_mod);
        }

        let limbs = |size: usize, limb_size: Option<usize>| -> Vec<BigUint> {
            let max = (one << size) - 1usize;
            let limb_size = limb_size.unwrap_or_else(|| div_ceil(size, n_limbs));
            let max_limb = (one << limb_size) - 1usize;
            let max_most_sign = &max >> ((n_limbs - 1) * limb_size);
            let limbs = std::iter::repeat_with(|| &max_limb)
                .take(n_limbs - 1)
                .chain(std::iter::once(&max_most_sign))
                .cloned()
                .collect_vec();

            // sanity check
            assert!(compose_uint(&limbs, limb_size) == max);

            limbs
        };

        let max_rem_limbs = limbs(max_rem.bits() as usize, Some(limb_size));
        let max_quot_limbs = limbs(max_quot.bits() as usize, Some(limb_size));

        let max_red_quot = (one << limb_size) - one;
        let max_unred = pseudo_wrong_mod * &max_red_quot;
        let max_unred_limbs = limbs(max_unred.bits() as usize - 1, None);

        let bases: Vec<_> = (0..n_limbs)
            .map(|i| BigUint::from(2usize).pow((i * limb_size) as u32))
            .map(|e| N::from_uint_red(&e))
            .collect();

        let pseudo_wrong_mod: Big<N> =
            Big::new(&pseudo_wrong_mod.clone().into(), n_limbs, limb_size);
        let rsh = bases.get(1).unwrap();
        let rsh = rsh.inv().unwrap();

        let wrong_mod_limbs = pseudo_wrong_mod.limbs_uint();
        let p_mul_q_max = product::<BigUint, _, _>(&wrong_mod_limbs[..], &max_quot_limbs[..]);
        let p_red_q_max = wrong_mod_limbs.iter().map(|e| e * &max_red_quot).collect();

        Self {
            n_limbs,
            limb_size,
            sublimb_size,
            mod_size,
            n_carries,
            native_mod,
            bases,
            rsh,
            max_unred,
            max_red_quot,
            max_rem,
            max_op,
            max_quot,
            max_quot_limbs,
            max_rem_limbs,
            max_unred_limbs,
            p_mul_q_max,
            p_red_q_max,
        }
    }

    pub(crate) fn big_from_assigned_limbs(
        &self,
        ac: &mut AbstractCircuit<N>,
        limbs: &[VarNum<N>],
        range: &Range,
    ) -> Result<VarBig<N>, Error> {
        // constraint native value
        let qc = izip!(limbs.iter(), self.bases.iter())
            .map(|(limb, base)| limb.var() * base)
            .collect_vec();
        let var = ac.eval(qc!() + qc);

        // calculate tracking bigint value
        let int = {
            let limbs: Value<Vec<_>> = Value::from_iter(limbs.iter().map(VarNum::int));
            limbs.map(|limbs| compose_int(limbs, self.limb_size))
        };

        // create varbig and return
        let max = self.max_value(range);
        let num = VarNum::overflow(&var, int.as_ref(), Some(&max));
        let big = VarBig::new(limbs, &num);
        ac.sanity_ok(|| self.validate_varbig(&big)).map(|_| big)
    }

    pub(crate) fn assign_limbs(
        &self,
        ac: &mut AbstractCircuit<N>,
        signed: bool,
        limbs: &[Value<BigInt>],
        range: &Range,
    ) -> Result<Vec<VarNum<N>>, Error> {
        let limbs = limbs.iter().map(|v| v.as_ref().map(Num::from_int_red));
        izip!(limbs, self.max_limbs(range))
            .map(|(limb, max)| {
                let nat = limb.as_ref().map(Num::nat);
                let int = limb.as_ref().map(Num::int);

                let var = if signed {
                    ac.decompose_assign_signed(self.sublimb_size, max.bits() as usize, &nat)?
                } else {
                    ac.decompose_assign(self.sublimb_size, max.bits() as usize, &nat)?
                };

                let limb = VarNum::overflow(&var, int, Some(&max));
                ac.sanity_ok(|| limb.validate())?;
                Ok(limb)
            })
            .try_collect()
    }

    pub(crate) fn _assign_internal(
        &self,
        ac: &mut AbstractCircuit<N>,
        int: Value<&BigInt>,
        signed: bool,
        range: &Range,
    ) -> Result<VarBig<N>, Error> {
        let n_limbs = self.n_limbs();
        let limb_size = self.limb_size();

        // decompose int annd range-assign limbs
        let limbs = int.map(|v| decompose_int(v, n_limbs, limb_size));
        let limbs = limbs.transpose_vec(n_limbs);
        let limbs = self.assign_limbs(ac, signed, &limbs, range)?;

        // constraint native value
        let qc = izip!(limbs.iter(), self.bases.iter())
            .map(|(limb, base)| limb.var() * base)
            .collect_vec();
        let var = ac.eval(qc!() + qc);

        // create varbig and return
        let num = VarNum::overflow(&var, int, Some(&self.max_value(range)));
        let big = VarBig::new(&limbs, &num);

        ac.sanity_ok(|| self.validate_varbig(&big)).map(|_| big)
    }

    pub(crate) fn assign(
        &self,
        ac: &mut AbstractCircuit<N>,
        int: Value<&BigUint>,
        range: &Range,
    ) -> Result<VarBig<N>, Error> {
        let int = int.map(|int| int.to_bigint().unwrap());
        int.as_ref()
            .map(|e| println!("assign: {}", e.to_str_radix(16)));
        self._assign_internal(ac, int.as_ref(), false, range)
    }

    pub(crate) fn assign_signed(
        &self,
        ac: &mut AbstractCircuit<N>,
        int: Value<&BigInt>,
        range: &Range,
    ) -> Result<VarBig<N>, Error> {
        self._assign_internal(ac, int, true, range)
    }

    pub(crate) fn get_constant(
        &self,
        ac: &mut AbstractCircuit<N>,
        constant: &BigUint,
    ) -> Result<VarBig<N>, Error> {
        fn get_num<N: Field>(
            ac: &mut AbstractCircuit<N>,
            constant: &Num<N>,
        ) -> Result<VarNum<N>, Error> {
            let nat = ac.get_constant(constant.nat());
            Ok(VarNum::overflow(
                &nat,
                constant.int().into(),
                Some(constant.uint()),
            ))
        }

        let constant = self.big_from_uint(constant);
        let limbs: Vec<_> = constant
            .limbs()
            .iter()
            .map(|num| get_num(ac, num))
            .try_collect()?;
        let nat = get_num(ac, constant.num())?;
        Ok(VarBig::new(&limbs, &nat))
    }

    pub(crate) fn eval_quad(
        &self,
        ac: &mut AbstractCircuit<N>,
        quad: &[Vec<QuadScaled<N>>],
        lin: &[Vec<Scaled<N>>],
        max_vals: Vec<usize>,
    ) {
        let n = self.n_carries;
        assert!(max_vals.len() >= n);
        let quad = quad.iter().map(Some).chain(std::iter::repeat(None)).take(n);
        let lin = lin.iter().map(Some).chain(std::iter::repeat(None)).take(n);
        let mut carry: Option<Var<N>> = None;
        izip!(quad, lin, max_vals).for_each(|(quad, lin, max)| {
            self.update_carry_qc(ac, &mut carry, max, qc!() + quad + lin)
        });
    }

    pub(crate) fn update_carry_qc(
        &self,
        ac: &mut AbstractCircuit<N>,
        carry: &mut Option<Var<N>>,
        max: usize,
        mut qc: Qc<N>,
    ) {
        qc += *carry;
        qc *= self.rsh;
        let carry_next: Var<N> = ac.eval(qc);
        ac.decompose_signed(self.sublimb_size, max, &carry_next)
            .unwrap();
        *carry = Some(carry_next);
    }

    pub fn select_from_table(
        &self,
        ac: &mut AbstractCircuit<N>,
        selector: &[Var<N>],
        table: &[VarBig<N>],
    ) -> Result<VarBig<N>, Error> {
        let limbs: Vec<_> = (0..self.n_limbs)
            .map(|i| {
                let table = table.iter().map(|el| el.limb_at(i)).cloned().collect_vec();
                ac.select_from_table(selector, &table)
            })
            .try_collect()?;
        let max_limbs = (0..self.n_limbs)
            .map(|i| table.iter().map(|e| e.max_at(i)).max().unwrap())
            .collect_vec();
        let limbs = izip!(limbs, max_limbs.iter())
            .map(|(limb, max)| VarNum::new(&limb, Some(max)))
            .collect_vec();
        self.big_from_assigned_limbs(ac, &limbs, &max_limbs.into())
    }

    pub fn select_from_constant_table(
        &self,
        ac: &mut AbstractCircuit<N>,
        selector: &[Var<N>],
        table: &[Big<N>],
    ) -> Result<VarBig<N>, Error> {
        let limbs: Vec<_> = (0..self.n_limbs)
            .map(|i| {
                let table = table.iter().map(|el| el.limb_at(i).nat()).collect_vec();
                ac.select_from_constant_table(selector, &table)
            })
            .try_collect()?;
        let max_limbs = (0..self.n_limbs)
            .map(|i| table.iter().map(|e| e.limb_at(i).uint()).max().unwrap())
            .collect_vec();
        let limbs = izip!(limbs, max_limbs.iter())
            .map(|(limb, max)| VarNum::new(&limb, Some(max)))
            .collect_vec();
        self.big_from_assigned_limbs(ac, &limbs, &max_limbs.into())
    }

    pub fn write(
        &self,
        ac: &mut AbstractCircuit<N>,
        segment: N,
        address: N,
        e: &VarBig<N>,
    ) -> Result<(), Error> {
        use crate::ir::mem::MemWriteOnceUnit;
        ac.write(segment, address, &e.limbs_var().cloned().collect_vec())
    }

    pub fn read(
        &self,
        ac: &mut AbstractCircuit<N>,
        segment: N,
        address_offset: N,
        address_fine: &Var<N>,
    ) -> Result<VarBig<N>, Error> {
        use crate::ir::mem::MemWriteOnceUnit;
        let limbs = ac.read(segment, address_offset, address_fine)?;
        let max_limbs = self.max_limbs(&Range::Remainder);
        let limbs = izip!(limbs, max_limbs)
            .map(|(limb, max)| VarNum::new(&limb, Some(&max)))
            .collect_vec();
        self.big_from_assigned_limbs(ac, &limbs, &Range::Remainder)
    }

    pub fn write_constant(
        &self,
        ac: &mut AbstractCircuit<N>,
        segment: N,
        address: N,
        e: &Big<N>,
    ) -> Result<(), Error> {
        use crate::ir::mem::MemReadOnlyUnit;
        ac.write(segment, address, &e.limbs_nat())
    }

    pub fn read_constant(
        &self,
        ac: &mut AbstractCircuit<N>,
        segment: N,
        address_offset: N,
        address_fine: &Var<N>,
    ) -> Result<VarBig<N>, Error> {
        use crate::ir::mem::MemReadOnlyUnit;
        let limbs = ac.read(segment, address_offset, address_fine)?;
        let max_limbs = self.max_limbs(&Range::Remainder);
        let limbs = izip!(limbs, max_limbs)
            .map(|(limb, max)| VarNum::new(&limb, Some(&max)))
            .collect_vec();
        self.big_from_assigned_limbs(ac, &limbs, &Range::Remainder)
    }
}
