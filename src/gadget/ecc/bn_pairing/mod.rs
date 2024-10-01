use super::{Coordinates, Point};
use crate::{
    gadget::big_field::{crt::CrtGadget, rns::Range, Big, VarBig},
    ir::ac::AbstractCircuit,
    Error, Field, Value,
};
use e12::E12;
use e2::E2;
use itertools::Itertools;
use num_bigint::BigUint;
use witness::BNPairing;

mod e12;
mod e2;
mod e6;
#[cfg(feature = "halo2")]
pub(crate) mod halo2;
mod witness;

impl<N: Field> Point<E2<VarBig<N>>> {
    pub fn transpose(&self) -> Value<Point<E2<BigUint>>> {
        let x = self.x().value();
        let y = self.y().value();
        x.zip(y).map(|(x, y)| Point::new(x, y))
    }
}

impl<N: Field> Point<VarBig<N>> {
    pub fn transpose(&self) -> Value<Point<BigUint>> {
        let x = self.x().uint();
        let y = self.y().uint();
        x.zip(y).map(|(x, y)| Point::new(x.clone(), y.clone()))
    }
}

pub struct BNPairingGadget<N: Field, Engine: BNPairing> {
    base_field: CrtGadget<N>,
    frobenius61: [E2<Big<N>>; 6],
    frobenius62: [E2<Big<N>>; 6],
    frobenius12: [E2<Big<N>>; 12],
    xi: E2<Big<N>>,
    b2: E2<Big<N>>,
    endo_u: E2<Big<N>>,
    endo_v: E2<Big<N>>,
    _marker: std::marker::PhantomData<Engine>,
}

pub(crate) const SIX_U_PLUS_2_NAF: [i8; 65] = [
    0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0,
    1, 1, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0,
    0, 1, 0, 1, 1,
];

const BN_X: u64 = 4965661367192848881;

pub(crate) fn constant_e2<N: Field>(crt: &CrtGadget<N>, e: &E2<BigUint>) -> E2<Big<N>> {
    let e0 = crt.rns().big_from_uint(&e.e0);
    let e1 = crt.rns().big_from_uint(&e.e1);
    E2::new(e0, e1)
}

impl<N: Field, Engine: BNPairing> BNPairingGadget<N, Engine> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        base_field: &CrtGadget<N>,
        frobenius61: [E2<BigUint>; 6],
        frobenius62: [E2<BigUint>; 6],
        frobenius12: [E2<BigUint>; 12],
        endo_u: E2<BigUint>,
        endo_v: E2<BigUint>,
        xi: E2<BigUint>,
        b2: E2<BigUint>,
    ) -> Self {
        let frobenius61 = frobenius61
            .iter()
            .map(|e| constant_e2(base_field, e))
            .collect_vec();

        let frobenius62 = frobenius62
            .iter()
            .map(|e| constant_e2(base_field, e))
            .collect_vec();

        let frobenius12 = frobenius12
            .iter()
            .map(|e| constant_e2(base_field, e))
            .collect_vec();

        let xi = constant_e2(base_field, &xi);
        let b2 = constant_e2(base_field, &b2);
        let endo_u = constant_e2(base_field, &endo_u);
        let endo_v = constant_e2(base_field, &endo_v);

        Self {
            base_field: base_field.clone(),
            frobenius61: frobenius61.try_into().unwrap(),
            frobenius62: frobenius62.try_into().unwrap(),
            frobenius12: frobenius12.try_into().unwrap(),
            endo_u,
            endo_v,
            xi,
            b2,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn assign_base_field(
        &self,
        ac: &mut AbstractCircuit<N>,
        value: Value<&BigUint>,
    ) -> Result<VarBig<N>, Error> {
        self.base_field.assign(ac, value, &Range::Remainder)
    }

    fn assert_on_g2(
        &self,
        ac: &mut AbstractCircuit<N>,
        p2: &Point<E2<VarBig<N>>>,
    ) -> Result<(), Error> {
        let y_square = &self.e2_square(ac, &p2.y);
        let x_square = &self.e2_square(ac, &p2.x);
        let x_cube = &self.e2_mul(ac, &p2.x, x_square);
        let x_cube_b = &self.e2_add_constant(ac, x_cube, &self.b2);
        self.e2_normal_equal(ac, x_cube_b, y_square)
    }

    pub fn assign_g2(
        &self,
        ac: &mut AbstractCircuit<N>,
        p2: &Value<Point<E2<BigUint>>>,
    ) -> Result<Point<E2<VarBig<N>>>, Error> {
        let (x, y) = p2
            .as_ref()
            .map(|p2| (p2.x().clone(), p2.y().clone()))
            .unzip();
        let x = self.e2_assign(ac, x)?;
        let y = self.e2_assign(ac, y)?;
        let p2 = Point::new(x, y);
        self.assert_on_g2(ac, &p2)?;
        self.assert_in_subgroup(ac, &p2)?;
        Ok(p2)
    }

    fn psi(&self, ac: &mut AbstractCircuit<N>, p: &Point<E2<VarBig<N>>>) -> Point<E2<VarBig<N>>> {
        let x = self.e2_conj(ac, &p.x);
        let y = self.e2_conj(ac, &p.y);
        let x = self.e2_mul_constant(ac, &x, &self.endo_u);
        let y = self.e2_mul_constant(ac, &y, &self.endo_v);
        Point::new(x, y)
    }

    fn assert_in_subgroup(
        &self,
        ac: &mut AbstractCircuit<N>,
        point: &Point<E2<VarBig<N>>>,
    ) -> Result<(), Error> {
        let mut x = point.clone();
        for i in (0..62).rev() {
            (x, _) = self.double(ac, &x)?;
            if (BN_X >> i) & 1 == 1 {
                (x, _) = self.add(ac, &x, point, false)?;
            }
        }
        let sx = self.psi(ac, &x);
        let ssx = self.psi(ac, &sx);
        let sssx = self.psi(ac, &ssx);

        let (mut u0, _) = self.add(ac, &ssx, &sx, false)?;
        (u0, _) = self.add(ac, &u0, &x, false)?;
        (u0, _) = self.add(ac, &u0, point, false)?;
        let (u1, _) = self.double(ac, &sssx)?;

        self.e2_normal_equal(ac, &u0.x, &u1.x)?;
        self.e2_normal_equal(ac, &u0.y, &u1.y)?;

        Ok(())
    }

    fn prepare_point(
        &self,
        ac: &mut AbstractCircuit<N>,
        p1: &[Point<VarBig<N>>],
    ) -> Vec<Point<VarBig<N>>> {
        p1.iter()
            .map(|p1| {
                let x_prime = self.base_field.div(ac, p1.x(), p1.y());
                let y_prime = self.base_field.div(ac, &x_prime, p1.x());
                let x_prime = self.base_field.neg(ac, &x_prime);
                let x_prime = self.base_field.reduce(ac, &x_prime);
                let y_prime = self.base_field.reduce(ac, &y_prime);
                Point::new(x_prime, y_prime)
            })
            .collect::<Vec<_>>()
    }

    #[allow(clippy::type_complexity)]
    fn double(
        &self,
        ac: &mut AbstractCircuit<N>,
        p: &Point<E2<VarBig<N>>>,
    ) -> Result<(Point<E2<VarBig<N>>>, E2<VarBig<N>>), Error> {
        let x_sq = self.e2_square(ac, &p.x);
        let x_sq3 = self.e2_triple(ac, &x_sq);
        let y2 = self.e2_double(ac, &p.y);
        let y2 = self.e2_inv(ac, &y2);
        let lambda = self.e2_mul(ac, &x_sq3, &y2);
        let x = self.e2_square_sub(ac, &lambda, &[&p.x, &p.x]);
        let t = self.e2_sub(ac, &p.x, &x);
        let t = self.e2_mul(ac, &lambda, &t);
        let y = self.e2_sub(ac, &t, &p.y);
        Ok((Point::new(x, y), lambda))
    }

    fn double_eval(
        &self,
        ac: &mut AbstractCircuit<N>,
        f: &mut E12<VarBig<N>>,
        acc: &mut Point<E2<VarBig<N>>>,
        p1: &Point<VarBig<N>>,
    ) {
        let (acc2, lambda) = self.double(ac, acc).unwrap();

        {
            let c1 = self.e2_mul_by_e(ac, &lambda, p1.x());
            let t = self.e2_mul(ac, &lambda, &acc.x);
            let t = self.e2_sub(ac, &t, &acc.y);
            let c3 = self.e2_mul_by_e(ac, &t, p1.y());
            *f = self.e12_reduce(ac, f);
            self.e12_mul_sparse(ac, f, &c1, &c3);
        }

        acc.x = self.e2_reduce(ac, &acc2.x);
        acc.y = self.e2_reduce(ac, &acc2.y);
    }

    #[allow(clippy::type_complexity)]
    fn add(
        &self,
        ac: &mut AbstractCircuit<N>,
        acc: &Point<E2<VarBig<N>>>,
        p2: &Point<E2<VarBig<N>>>,
        negate: bool,
    ) -> Result<(Point<E2<VarBig<N>>>, E2<VarBig<N>>), Error> {
        let lambda = {
            let t0 = self.e2_sub(ac, &acc.x, &p2.x);
            let t0 = self.e2_inv(ac, &t0);
            let t1 = if negate {
                self.e2_add(ac, &acc.y, &p2.y)
            } else {
                self.e2_sub(ac, &acc.y, &p2.y)
            };
            self.e2_mul(ac, &t0, &t1)
        };

        let x = self.e2_square_sub(ac, &lambda, &[&acc.x, &p2.x]);
        let t0 = self.e2_mul_sub(ac, &lambda, &acc.x, &acc.y);
        let y = {
            let t1 = self.e2_mul(ac, &lambda, &x);
            self.e2_sub(ac, &t0, &t1)
        };
        Ok((Point::new(x, y), lambda))
    }

    fn add_eval(
        &self,
        ac: &mut AbstractCircuit<N>,
        f: &mut E12<VarBig<N>>,
        acc: &mut Point<E2<VarBig<N>>>,
        p2: &Point<E2<VarBig<N>>>,
        p1: &Point<VarBig<N>>,
        negate: bool,
    ) {
        let (acc2, lambda) = self.add(ac, acc, p2, negate).unwrap();

        let t0 = self.e2_mul_sub(ac, &lambda, &acc.x, &acc.y);
        let c1 = self.e2_mul_by_e(ac, &lambda, p1.x());
        let c3 = self.e2_mul_by_e(ac, &t0, p1.y());

        *f = self.e12_reduce(ac, f);
        self.e12_mul_sparse(ac, f, &c1, &c3);

        acc.x = acc2.x;
        acc.y = acc2.y;
    }

    fn eval_fixed(
        &self,
        ac: &mut AbstractCircuit<N>,
        f: &mut E12<VarBig<N>>,
        lambda: &E2<Big<N>>,
        coeff: &E2<Big<N>>,
        p1: &Point<VarBig<N>>,
    ) {
        let c1 = self.e2_mul_by_constant_e(ac, lambda, p1.x());
        let c3 = self.e2_mul_by_constant_e(ac, coeff, p1.y());
        self.e12_mul_sparse(ac, f, &c1, &c3);
    }

    fn double_fixed(
        &self,
        ac: &mut AbstractCircuit<N>,
        f: &mut E12<VarBig<N>>,
        acc: &mut Point<E2<BigUint>>,
        p1: &Point<VarBig<N>>,
    ) {
        let (lambda, coeff) = Engine::double(acc);
        let lambda = constant_e2(&self.base_field, &lambda);
        let coeff = constant_e2(&self.base_field, &coeff);
        self.eval_fixed(ac, f, &lambda, &coeff, p1)
    }

    fn add_fixed(
        &self,
        ac: &mut AbstractCircuit<N>,
        f: &mut E12<VarBig<N>>,
        acc: &mut Point<E2<BigUint>>,
        p2: &Point<E2<BigUint>>,
        p1: &Point<VarBig<N>>,
        neg: bool,
    ) {
        let (lambda, coeff) = Engine::add(acc, p2, neg);
        let lambda = constant_e2(&self.base_field, &lambda);
        let coeff = constant_e2(&self.base_field, &coeff);
        self.eval_fixed(ac, f, &lambda, &coeff, p1)
    }

    fn residue_check(
        &self,
        ac: &mut AbstractCircuit<N>,
        c_inv: &E12<VarBig<N>>,
        c: &E12<VarBig<N>>,
        f: &E12<VarBig<N>>,
        cube_shift: Value<usize>,
    ) -> Result<(), Error> {
        // f = f * c^(-q) * c^(2q) * c^(-3q)
        let f = {
            let u1 = self.e12_frobenius_map(ac, c_inv, 1);
            let u2 = self.e12_frobenius_map(ac, c, 2);
            let u3 = self.e12_frobenius_map(ac, c_inv, 3);

            let f = self.e12_mul(ac, f, &u1);
            let f = self.e12_mul(ac, &f, &u2);
            self.e12_mul(ac, &f, &u3)
        };

        // Get the correct non residue shifter
        let w0 = self.e12_one(ac);
        let w1 = self.e12_constant(ac, Engine::w1()).unwrap();
        let w2 = self.e12_constant(ac, Engine::w2()).unwrap();

        let (b0, b1) = cube_shift
            .map(|cube_shift| match cube_shift {
                0 => (N::zero(), N::zero()),
                1 => (N::one(), N::zero()),
                2 => (N::zero(), N::one()),
                _ => unreachable!(),
            })
            .unzip();
        let b0 = ac.assign_bit(&b0).unwrap();
        let b1 = ac.assign_bit(&b1).unwrap();

        let s = self.e12_select(ac, &b0, &w0, &w1).unwrap();
        let s = self.e12_select(ac, &b1, &s, &w2).unwrap();

        // expect `f * c^(-q) * c^(2q) * c^(-3q) * s == 1``
        let must_be_one = self.e12_mul(ac, &f, &s);
        let one = self.e12_one(ac);
        let must_be_zero = self.e12_sub(ac, &must_be_one, &one);
        self.e12_assert_zero(ac, &must_be_zero)
    }

    pub fn pairing_check_mixed(
        &self,
        ac: &mut AbstractCircuit<N>,
        p1_var: &[Point<VarBig<N>>],
        p2_var: &[Point<E2<VarBig<N>>>],
        p1_fix: &[Point<VarBig<N>>],
        p2_fix: &[Point<E2<BigUint>>],
    ) -> Result<(), Error> {
        let (c, cube_shift) = {
            let p1: Value<Vec<_>> =
                Value::from_iter(p1_var.iter().chain(p1_fix).map(|p1| p1.transpose()));
            let p2_var: Value<Vec<_>> = Value::from_iter(p2_var.iter().map(|p2| p2.transpose()));
            p1.zip(p2_var)
                .map(|(p1, p2_var)| {
                    let p2 = p2_var.iter().chain(p2_fix).cloned().collect_vec();
                    Engine::final_exp_witness(&p1, &p2)
                })
                .unzip()
        };

        assert_eq!(p1_var.len(), p2_var.len());
        assert_eq!(p1_fix.len(), p2_fix.len());

        let c = self.e12_assign(ac, c)?;
        let c_inv = self.e12_inverse(ac, &c)?;
        let mut f = c_inv.clone();
        let mut acc_var = p2_var.to_vec();
        let mut acc_fix = p2_fix.to_vec();

        // Prepare for simpler line equation
        let p1_var = self.prepare_point(ac, p1_var);
        let p1_fix = self.prepare_point(ac, p1_fix);

        // Run residue embedded miller loop
        for x in SIX_U_PLUS_2_NAF.iter().rev().skip(1) {
            f = self.e12_reduce(ac, &f);
            f = self.e12_square(ac, &f);

            p1_var
                .iter()
                .zip(acc_var.iter_mut())
                .for_each(|(p1, acc)| self.double_eval(ac, &mut f, acc, p1));

            p1_fix
                .iter()
                .zip(acc_fix.iter_mut())
                .for_each(|(p1, acc)| self.double_fixed(ac, &mut f, acc, p1));

            #[allow(clippy::single_match)]
            match x {
                val @ (1 | -1) => {
                    let (negate, scale) = match val {
                        1 => (false, &c_inv),
                        -1 => (true, &c),
                        _ => unreachable!(),
                    };

                    f = self.e12_reduce(ac, &f);
                    f = self.e12_mul(ac, &f, scale);

                    p1_var
                        .iter()
                        .zip(p2_var.iter())
                        .zip(acc_var.iter_mut())
                        .for_each(|((p1, p2), acc)| self.add_eval(ac, &mut f, acc, p2, p1, negate));

                    p1_fix
                        .iter()
                        .zip(p2_fix.iter())
                        .zip(acc_fix.iter_mut())
                        .for_each(|((p1, p2), acc)| {
                            self.add_fixed(ac, &mut f, acc, p2, p1, negate)
                        });
                }
                _ => {}
            }
        }

        {
            // In sake of simplicity we will assign fixed points in the last step
            let p1 = p1_var.iter().chain(p1_fix.iter()).collect_vec();
            let p2_fix = p2_fix
                .iter()
                .map(|p2| self.assign_g2(ac, &Value::new(p2.clone())).unwrap())
                .collect_vec();
            let p2 = p2_var.iter().chain(p2_fix.iter()).cloned().collect_vec();
            let acc_fix = acc_fix
                .iter()
                .map(|acc| self.assign_g2(ac, &Value::new(acc.clone())).unwrap())
                .collect_vec();
            let mut acc = acc_var.iter().chain(acc_fix.iter()).cloned().collect_vec();

            p1.iter()
                .zip(p2.iter())
                .zip(acc.iter_mut())
                .for_each(|((p1, p2), acc)| {
                    let mut p2 = p2.clone();
                    p2.x = self.e2_conj(ac, &p2.x);
                    p2.x = self.e2_mul_constant(ac, &p2.x, &self.frobenius61[1]);
                    p2.y = self.e2_conj(ac, &p2.y);
                    p2.y = self.e2_mul_constant(ac, &p2.y, &self.xi);
                    self.add_eval(ac, &mut f, acc, &p2, p1, false)
                });

            p1.iter()
                .zip(p2.iter())
                .zip(acc.iter_mut())
                .for_each(|((p1, p2), acc)| {
                    let mut p2 = p2.clone();
                    p2.x = self.e2_mul_constant(ac, &p2.x, &self.frobenius61[2]);
                    self.add_eval(ac, &mut f, acc, &p2, p1, false)
                });
        }

        self.residue_check(ac, &c_inv, &c, &f, cube_shift)?;

        Ok(())
    }

    pub fn pairing_check(
        &self,
        ac: &mut AbstractCircuit<N>,
        p1: &[Point<VarBig<N>>],
        p2: &[Point<E2<VarBig<N>>>],
    ) -> Result<(), Error> {
        self.pairing_check_mixed(ac, p1, p2, &[], &[])
    }
}
