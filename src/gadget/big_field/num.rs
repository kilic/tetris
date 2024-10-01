use crate::ir::combination::CombinationIR;
use crate::{
    ir::{ac::AbstractCircuit, combination::CombinationGadget},
    qc,
    utils::{compose_int, decompose_int, select},
    Error, Field, QuadScaled, Scaled, Term, Value, Var,
};
use itertools::{izip, Itertools};
use num_bigint::{BigInt, BigUint};
use num_traits::Signed;
use num_traits::Zero;
use std::ops::Neg;

#[derive(Clone)]
pub struct Num<N> {
    pub(crate) nat: N,
    pub(crate) int: BigInt,
}

impl<N: Field> std::fmt::Debug for Num<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut f = f.debug_struct("Num");
        let f = f.field("nat", &self.nat);
        f.field("int", &self.int.to_str_radix(16));
        f.field("bits", &self.int.bits());
        f.finish()
    }
}

impl<N: Field> Neg for Num<N> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        (&self).neg()
    }
}

impl<N: Field> Neg for &Num<N> {
    type Output = Num<N>;
    fn neg(self) -> Self::Output {
        Num {
            nat: self.nat.neg(),
            int: self.int.clone().neg(),
        }
    }
}

impl<N: Field> From<u64> for Num<N> {
    fn from(e: u64) -> Self {
        Self {
            nat: N::from_u64(e),
            int: e.into(),
        }
    }
}

impl<N: Field> Num<N> {
    pub fn zero() -> Self {
        use num_traits::Zero;
        Self {
            nat: N::zero(),
            int: BigInt::zero(),
        }
    }

    pub fn one() -> Self {
        use num_traits::One;
        Self {
            nat: N::one(),
            int: BigInt::one(),
        }
    }

    pub fn from_uint_red(uint: &BigUint) -> Self {
        Self {
            nat: N::from_uint_red(uint),
            int: uint.clone().into(),
        }
    }

    pub fn from_uint(uint: &BigUint) -> Result<Self, Error> {
        Ok(Self {
            nat: N::from_uint(uint)?,
            int: uint.clone().into(),
        })
    }

    pub fn from_int_red(int: &BigInt) -> Self {
        Self {
            nat: N::from_int_red(int),
            int: int.clone(),
        }
    }

    pub fn from_int(int: &BigInt) -> Result<Self, Error> {
        Ok(Self {
            nat: N::from_int(int)?,
            int: int.clone(),
        })
    }

    pub fn from_nat(nat: N) -> Self {
        Self {
            nat,
            int: nat.int(),
        }
    }

    pub fn compose(limbs: &[Num<N>], limb_size: usize) -> Self {
        let int = compose_int(limbs.iter().map(Num::int), limb_size);
        let limbs = limbs.iter().map(Num::nat).collect_vec();
        let nat = N::compose(&limbs, limb_size);
        Self { nat, int }
    }

    pub fn decompose(&self, n_limbs: usize, limb_size: usize) -> Vec<Num<N>> {
        let limbs = decompose_int(self.int(), n_limbs, limb_size);
        limbs.iter().map(Self::from_int_red).collect_vec()
    }

    pub fn nat(&self) -> N {
        self.nat
    }

    pub fn int(&self) -> &BigInt {
        &self.int
    }

    pub fn uint(&self) -> &BigUint {
        assert!(!self.int.is_negative());
        self.mag()
    }

    pub fn mag(&self) -> &BigUint {
        self.int.magnitude()
    }

    pub fn is_zero(&self) -> bool {
        use num_traits::Zero;
        self.int.is_zero()
    }

    pub fn is_negative(&self) -> bool {
        self.int.is_negative()
    }

    pub fn validate(&self) -> Result<(), Error> {
        (N::from_int_red(self.int()) == self.nat)
            .then_some(())
            .ok_or(Error::Invalid)
    }
}

#[derive(Clone)]
// Big number decomposed into limbs and with native field and overflow value tracking
pub struct Big<N> {
    pub(crate) limbs: Vec<Num<N>>,
    pub(crate) num: Num<N>,
}

impl<N: Field> std::fmt::Debug for Big<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut f = f.debug_struct("Big");
        let f = f.field("limbs", &self.limbs);
        f.field("num", &self.num);
        f.finish()
    }
}

impl<N: Field> Big<N> {
    pub fn new(e: &BigInt, n_limbs: usize, limb_size: usize) -> Self {
        let num = Num::from_int_red(e);
        let limbs = num.decompose(n_limbs, limb_size);
        Self { limbs, num }
    }

    pub fn from_limbs(limbs: &[BigInt], limb_size: usize) -> Self {
        let limbs = limbs.iter().map(Num::from_int_red).collect_vec();
        let num = Num::compose(&limbs, limb_size);
        Self { limbs, num }
    }

    pub fn modulus<W: Field>(n_limbs: usize, limb_size: usize) -> Self {
        Self::new(&W::modulus().into(), n_limbs, limb_size)
    }

    pub fn n_limbs(&self) -> usize {
        self.limbs.len()
    }

    // Returns overflow and native value
    pub fn num(&self) -> &Num<N> {
        &self.num
    }

    // Returns overflow value as BigInt
    pub fn int(&self) -> &BigInt {
        self.num.int()
    }

    // Returns overflow value as BigUint
    // Will fail if the value is negative
    pub fn uint(&self) -> &BigUint {
        self.num.uint()
    }

    // Returns native value
    pub fn nat(&self) -> N {
        self.num.nat()
    }

    pub fn neg(&self) -> Self {
        Big {
            limbs: self.limbs.iter().map(Neg::neg).collect_vec(),
            num: self.num.clone().neg(),
        }
    }

    pub fn is_zero(&self) -> bool {
        self.int().is_zero()
    }

    pub fn is_negative(&self) -> bool {
        self.num.is_negative()
    }

    pub fn limbs(&self) -> &[Num<N>] {
        &self.limbs
    }

    pub fn limb_at(&self, idx: usize) -> &Num<N> {
        self.limbs.get(idx).unwrap()
    }

    pub fn limbs_uint(&self) -> Vec<BigUint> {
        self.limbs.iter().map(Num::uint).cloned().collect_vec()
    }

    pub fn limbs_nat(&self) -> Vec<N> {
        self.limbs.iter().map(Num::nat).collect_vec()
    }

    pub fn validate(&self, limb_size: usize) -> Result<(), Error> {
        self.num.validate()?;
        self.limbs.iter().try_for_each(Num::validate)?;
        // compose native value
        let nat = N::compose(&self.limbs_nat(), limb_size);
        (nat == self.num.nat())
            .then_some(())
            .ok_or(Error::Invalid)?;
        // compose overflow value
        let int = &compose_int(self.limbs.iter().map(Num::int), limb_size);
        (int == self.num.int())
            .then_some(())
            .ok_or(Error::Invalid)?;
        Ok(())
    }

    pub fn cast<W: Field>(&self) -> Result<W, Error> {
        W::from_int(self.int())
    }
}

// Variable number decomposed into limbs and with native field, overflow and max value tracking
#[derive(Clone)]
pub struct VarNum<N: Field> {
    var: Var<N>,
    int: Value<BigInt>,
    max: Option<BigUint>,
}

impl<N: Field> std::fmt::Debug for VarNum<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut f = f.debug_struct("VarNum");
        let f = f.field("var", &self.var);
        self.int.as_ref().map(|e| {
            f.field("int", &e.to_str_radix(16));
            f.field("bits", &e.bits());
        });
        if let Some(e) = &self.max {
            f.field("max", &e.to_str_radix(16));
            f.field("bits", &e.bits());
        }
        f.finish()
    }
}

impl<N: Field> VarNum<N> {
    pub fn overflow(var: &Var<N>, int: Value<&BigInt>, max: Option<&BigUint>) -> Self {
        Self {
            int: int.cloned(),
            var: *var,
            max: max.cloned(),
        }
    }

    pub fn new(var: &Var<N>, max: Option<&BigUint>) -> Self {
        let int = var.int();
        Self {
            int,
            var: *var,
            max: max.cloned(),
        }
    }

    pub fn num(&self) -> Value<Num<N>> {
        self.var.value().zip(self.int()).map(|(nat, int)| Num {
            nat,
            int: int.clone(),
        })
    }

    pub fn validate(&self) -> Result<(), Error> {
        // check big int <-> native value equivalence
        self.num().validate(Num::validate)?;
        // check max values
        self.int.validate(|int| {
            if let Some(max) = self.max() {
                (int.magnitude() <= max).then_some(()).ok_or(Error::Invalid)
            } else {
                Ok(())
            }
        })?;
        Ok(())
    }

    pub fn var(&self) -> &Var<N> {
        &self.var
    }

    pub fn int(&self) -> Value<&BigInt> {
        self.int.as_ref()
    }

    pub fn uint(&self) -> Value<&BigUint> {
        self.int.as_ref().map(|e| {
            assert!(!e.is_negative());
            e.magnitude()
        })
    }

    pub fn max(&self) -> Option<&BigUint> {
        self.max.as_ref()
    }

    pub fn select(
        &self,
        ac: &mut AbstractCircuit<N>,
        cond: &Var<N>,
        other: &Self,
    ) -> Result<Self, Error> {
        let max = std::cmp::max(self.max(), other.max()).unwrap();
        let sel = ac.select(cond, self.var(), other.var())?;
        let int = cond
            .value()
            .zip(self.int().zip(other.int()))
            .map(|(cond, (w0, w1))| select(cond == N::zero(), w0, w1));
        Ok(Self::overflow(&sel, int, Some(max)))
    }

    pub fn select_constant(
        ac: &mut AbstractCircuit<N>,
        cond: &Var<N>,
        a0: &Num<N>,
        a1: &Num<N>,
    ) -> Result<Self, Error> {
        let max = &std::cmp::max(a0.uint(), a1.uint());
        let sel = ac.select_constant(cond, a0.nat(), a1.nat())?;
        let int = cond
            .value()
            .map(|c| select(c == N::zero(), a0.int(), a1.int()));
        Ok(Self::overflow(&sel, int, Some(max)))
    }

    pub fn add(&self, ac: &mut AbstractCircuit<N>, other: &Self) -> Self {
        let var = ac.add(self.var(), other.var());
        let int = self.int() + other.int();
        let max = self.max().zip(other.max()).map(|(a, b)| a + b);
        VarNum::overflow(&var, int.as_ref(), max.as_ref())
    }

    pub fn double(&self, ac: &mut AbstractCircuit<N>) -> Self {
        self.mul_small(ac, 2)
    }

    pub fn triple(&self, ac: &mut AbstractCircuit<N>) -> Self {
        self.mul_small(ac, 3)
    }

    pub fn add_constant(&self, ac: &mut AbstractCircuit<N>, constant: &Num<N>) -> Self {
        let var = ac.add_constant(self.var(), constant.nat());
        let int = self.int() + constant.int();
        let max = self.max().map(|max| max + constant.uint());
        VarNum::overflow(&var, int.as_ref(), max.as_ref())
    }

    pub fn sub_from_constant(&self, ac: &mut AbstractCircuit<N>, constant: &Num<N>) -> Self {
        use crate::ir::combination::quad::Qc;
        let qc = qc!(constant.nat()) - self.var();
        let var = ac.eval(qc);
        let int = self.int().neg() + constant.int();
        let max = self.max().map(|max| max + constant.uint());
        VarNum::overflow(&var, int.as_ref(), max.as_ref())
    }

    pub fn sub(&self, ac: &mut AbstractCircuit<N>, other: &Self) -> Self {
        let var = ac.sub(self.var(), other.var());
        let int = self.int() - other.int();
        let max = self.max().zip(other.max()).map(|(a, b)| a + b);
        VarNum::overflow(&var, int.as_ref(), max.as_ref())
    }

    pub fn mul_small(&self, ac: &mut AbstractCircuit<N>, other: u64) -> Self {
        let var = ac.scale(&(self.var() * N::from_u64(other)));
        let int = self.int().map(|e| e * other);
        let max = self.max().map(|max| max * other);
        VarNum::overflow(&var, int.as_ref(), max.as_ref())
    }
}

#[derive(Debug, Clone)]
pub struct VarBig<N: Field> {
    limbs: Vec<VarNum<N>>,
    num: VarNum<N>,
}

impl<N: Field> VarBig<N> {
    pub fn new(limbs: &[VarNum<N>], num: &VarNum<N>) -> Self {
        Self {
            limbs: limbs.to_vec(),
            num: num.clone(),
        }
    }

    pub fn validate(&self, limb_size: usize) -> Result<(), Error> {
        self.num.validate()?;
        self.limbs.iter().try_for_each(VarNum::validate)?;
        self.big().validate(|big| big.validate(limb_size))?;
        Ok(())
    }

    pub fn cast<W: Field>(&self) -> Result<Value<W>, Error> {
        self.uint().map(|uint| W::from_uint(uint)).ok()
    }

    pub fn limb_at(&self, idx: usize) -> &Var<N> {
        self.limbs.get(idx).unwrap().var()
    }

    pub fn limbs(&self) -> impl Iterator<Item = &VarNum<N>> {
        self.limbs.iter()
    }

    pub fn limbs_var(&self) -> impl Iterator<Item = &Var<N>> {
        self.limbs.iter().map(VarNum::var)
    }

    pub fn max_limbs(&self) -> Vec<BigUint> {
        self.limbs
            .iter()
            .filter_map(VarNum::max)
            .cloned()
            .collect_vec()
    }

    pub fn max_at(&self, idx: usize) -> &BigUint {
        self.limbs.get(idx).unwrap().max().unwrap()
    }

    pub fn int(&self) -> Value<&BigInt> {
        self.num.int()
    }

    pub fn uint(&self) -> Value<&BigUint> {
        self.num.uint()
    }

    pub fn nat(&self) -> &Var<N> {
        self.num.var()
    }

    pub fn max(&self) -> Option<&BigUint> {
        self.num.max()
    }

    pub fn big(&self) -> Value<Big<N>> {
        let num = self.num.num();
        let limbs = Value::from_iter(self.limbs.iter().map(VarNum::num));
        limbs.zip(num).map(|(limbs, num)| Big { limbs, num })
    }

    pub fn copy_equal(&self, ac: &mut AbstractCircuit<N>, other: &VarBig<N>) -> Result<(), Error> {
        self.limbs()
            .zip(other.limbs())
            .try_for_each(|(w0, w1)| ac.equal(w0.var(), w1.var()))
    }

    pub fn add(&self, ac: &mut AbstractCircuit<N>, other: &VarBig<N>) -> VarBig<N> {
        let limbs = izip!(self.limbs.iter(), other.limbs.iter())
            .map(|(a, b)| a.add(ac, b))
            .collect_vec();
        let nat = self.num.add(ac, &other.num);
        VarBig::new(&limbs, &nat)
    }

    pub fn double(&self, ac: &mut AbstractCircuit<N>) -> VarBig<N> {
        let limbs = self.limbs.iter().map(|a| a.double(ac)).collect_vec();
        let nat = self.num.double(ac);
        VarBig::new(&limbs, &nat)
    }

    pub fn triple(&self, ac: &mut AbstractCircuit<N>) -> VarBig<N> {
        let limbs = self.limbs.iter().map(|a| a.triple(ac)).collect_vec();
        let nat = self.num.triple(ac);
        VarBig::new(&limbs, &nat)
    }

    pub fn mul_small(&self, ac: &mut AbstractCircuit<N>, e: u64) -> VarBig<N> {
        let limbs = self.limbs.iter().map(|a| a.mul_small(ac, e)).collect_vec();
        let nat = self.num.mul_small(ac, e);
        VarBig::new(&limbs, &nat)
    }

    pub fn sub(&self, ac: &mut AbstractCircuit<N>, other: &VarBig<N>) -> VarBig<N> {
        let limbs = izip!(self.limbs.iter(), other.limbs.iter())
            .map(|(a, b)| a.sub(ac, b))
            .collect_vec();
        let nat = self.num.sub(ac, &other.num);
        VarBig::new(&limbs, &nat)
    }

    pub fn add_constant(&self, ac: &mut AbstractCircuit<N>, other: &Big<N>) -> VarBig<N> {
        let limbs = izip!(self.limbs.iter(), other.limbs.iter())
            .map(|(a, b)| a.add_constant(ac, b))
            .collect_vec();
        let nat = self.num.add_constant(ac, &other.num);
        VarBig::new(&limbs, &nat)
    }

    pub fn sub_from_constant(&self, ac: &mut AbstractCircuit<N>, other: &Big<N>) -> VarBig<N> {
        let limbs = izip!(self.limbs.iter(), other.limbs.iter())
            .map(|(a, b)| a.sub_from_constant(ac, b))
            .collect_vec();
        let nat = self.num.sub_from_constant(ac, &other.num);
        VarBig::new(&limbs, &nat)
    }

    pub fn select(
        &self,
        ac: &mut AbstractCircuit<N>,
        cond: &Var<N>,
        other: &VarBig<N>,
    ) -> Result<VarBig<N>, Error> {
        let limbs: Vec<_> = self
            .limbs
            .iter()
            .zip(other.limbs.iter())
            .map(|(w0, w1)| w0.select(ac, cond, w1))
            .try_collect()?;
        let nat = self.num.select(ac, cond, &other.num)?;
        Ok(VarBig::new(&limbs, &nat))
    }

    pub fn product(&self, other: &Self) -> Vec<Vec<QuadScaled<N>>> {
        assert_eq!(self.limbs.len(), other.limbs.len());
        let size = self.limbs.len() * 2 - 1;
        let mut prod = vec![vec![]; size];
        self.limbs_var().enumerate().for_each(|(i, w0)| {
            other
                .limbs_var()
                .enumerate()
                .for_each(|(j, w1)| prod[i + j].push(w0 * w1));
        });
        prod
    }

    pub fn product_constant(&self, other: &Big<N>) -> Vec<Vec<Scaled<N>>> {
        assert_eq!(self.limbs.len(), other.limbs.len());
        let size = self.limbs.len() * 2 - 1;
        let mut prod = vec![vec![]; size];
        self.limbs_var().enumerate().for_each(|(i, w0)| {
            other
                .limbs_nat()
                .iter()
                .enumerate()
                .for_each(|(j, w1)| prod[i + j].push(w0 * w1));
        });
        prod
    }
}
