use super::{Coordinates, Point};
use crate::{
    gadget::big_field::{crt::CrtGadget, rns::Range, Big, VarBig},
    ir::ac::AbstractCircuit,
    Error, Field, Value,
};
use e6::E6;
use itertools::Itertools;
use num_bigint::BigUint;
use witness::Bw6Pairing;

use super::{ecc_general::GeneralEccGadget, Curve};

mod e3;
mod e6;
pub mod halo2;
pub mod witness;

// x+1
// Alligned with LOOP_2_NAF
pub(super) const LOOP_1_NAF: [i8; 190] = [
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
];

// x^3-x^2-x
// 0x23ed1347970dec008a442f991fffffffffffffffffffffff
pub(super) const LOOP_2_NAF: [i8; 190] = [
    -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
    0, 1, 0, 0, -1, 0, 1, 0, -1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0,
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, -1, 0, 0, -1,
    0, 1, 0, -1, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 1, 0, 1, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0,
    1, 0, 0, 1,
];

impl<N: Field> Point<VarBig<N>> {
    pub fn transpose(&self) -> Value<Point<BigUint>> {
        let x = self.x().uint();
        let y = self.y().uint();
        x.zip(y).map(|(x, y)| Point::new(x.clone(), y.clone()))
    }
}

pub struct Bw6PairingGadget<N: Field, G1: Curve, G2: Curve, Pairing: Bw6Pairing> {
    base_field_crt: CrtGadget<N>,
    _g1: GeneralEccGadget<G1, N>,
    _g2: GeneralEccGadget<G2, N>,
    // pairing: Pairing,
    zeta: Big<N>,
    frobenius_3c1: Big<N>,
    frobenius_3c2: Big<N>,
    frobenius_6c1: Big<N>,
    _marker: std::marker::PhantomData<Pairing>,
}

impl<N: Field, G1: Curve, G2: Curve, Pairing: Bw6Pairing> Bw6PairingGadget<N, G1, G2, Pairing> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        base_field_crt: CrtGadget<N>,
        g1: GeneralEccGadget<G1, N>,
        g2: GeneralEccGadget<G2, N>,

        zeta: Big<N>,
        frobenius_3c1: Big<N>,
        frobenius_3c2: Big<N>,
        frobenius_6c1: Big<N>,
    ) -> Self {
        Self {
            base_field_crt,
            _g1: g1,
            _g2: g2,
            zeta,
            frobenius_3c1,
            frobenius_3c2,
            frobenius_6c1,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn assign_base_field(
        &self,
        ac: &mut AbstractCircuit<N>,
        value: Value<&BigUint>,
    ) -> Result<VarBig<N>, Error> {
        self.base_field_crt.assign(ac, value, &Range::Remainder)
    }

    fn prepare_point(
        &self,
        ac: &mut AbstractCircuit<N>,
        p1: &[Point<VarBig<N>>],
    ) -> Vec<Point<VarBig<N>>> {
        let crt = &self.base_field_crt;
        p1.iter()
            .map(|p1| {
                let x_prime = crt.div(ac, p1.x(), p1.y());
                let y_prime = crt.div(ac, &x_prime, p1.x());
                let x_prime = crt.neg(ac, &x_prime);
                let x_prime = crt.reduce(ac, &x_prime);
                let y_prime = crt.reduce(ac, &y_prime);
                Point::new(x_prime, y_prime)
            })
            .collect::<Vec<_>>()
    }

    fn double(
        &self,
        ac: &mut AbstractCircuit<N>,
        point: &Point<VarBig<N>>,
    ) -> (Point<VarBig<N>>, VarBig<N>) {
        let crt = &self.base_field_crt;
        // lambda = (3 * a_x^2) / 2 * a_y
        let x_square = &crt.square(ac, &point.x, &[], &[]);
        let numer = &x_square.triple(ac);
        let denom = &point.y.double(ac);
        let lambda = crt.div(ac, numer, denom);
        // c_x = lambda * lambda - 2 * a_x
        let x = crt.square(ac, &lambda, &[], &[&point.x, &point.x]);
        // c_y = lambda * (a_x - c_x) - a_y
        let t = &point.x.sub(ac, &x);
        let y = crt.mul(ac, &lambda, t, &[], &[&point.y]);
        (Point::new(x, y), lambda)
    }

    fn double_eval(
        &self,
        ac: &mut AbstractCircuit<N>,
        f: &mut E6<VarBig<N>>,
        acc: &mut Point<VarBig<N>>,
        p1: &Point<VarBig<N>>,
    ) {
        let crt = &self.base_field_crt;
        let (acc2, lambda) = self.double(ac, acc);
        let nu = crt.mul(ac, &lambda, &acc.x, &[], &[&acc.y]);
        let u1 = crt.mul(ac, &lambda, p1.x(), &[], &[]);
        let u0 = crt.mul(ac, &nu, p1.y(), &[], &[]);

        self.e6_mul_sparse(ac, f, &u0, &u1);
        acc.x = acc2.x;
        acc.y = acc2.y;
    }

    fn double_eval_fixed(
        &self,
        ac: &mut AbstractCircuit<N>,
        f: &mut E6<VarBig<N>>,
        acc: &mut Point<BigUint>,
        p1: &Point<VarBig<N>>,
    ) {
        let (lambda, nu) = Pairing::double(acc);
        let lambda = self.base_field_crt.rns().big_from_uint(&lambda);
        let nu = self.base_field_crt.rns().big_from_uint(&nu);
        let u1 = self
            .base_field_crt
            .mul_constant(ac, p1.x(), &lambda, &[], &[]);
        let u0 = self.base_field_crt.mul_constant(ac, p1.y(), &nu, &[], &[]);
        self.e6_mul_sparse(ac, f, &u0, &u1);
    }

    fn add(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &Point<VarBig<N>>,
        b: &Point<VarBig<N>>,
        neg: bool,
    ) -> (Point<VarBig<N>>, VarBig<N>) {
        let crt = &self.base_field_crt;
        // lambda = b_y - a_y / b_x - a_x
        let numer = if !neg {
            &a.y.sub(ac, &b.y)
        } else {
            &a.y.add(ac, &b.y)
        };

        let denom = &a.x.sub(ac, &b.x);

        let lambda = crt.div(ac, numer, denom);
        let x = crt.square(ac, &lambda, &[], &[&a.x, &b.x]);
        let t = &a.x.sub(ac, &x);
        let y = crt.mul(ac, t, &lambda, &[], &[&a.y]);
        (Point::new(x, y), lambda)
    }

    fn add_eval(
        &self,
        ac: &mut AbstractCircuit<N>,
        f: &mut E6<VarBig<N>>,
        acc: &mut Point<VarBig<N>>,
        p2: &Point<VarBig<N>>,
        p1: &Point<VarBig<N>>,
        neg: bool,
    ) {
        let crt = &self.base_field_crt;
        let (acc2, lambda) = self.add(ac, acc, p2, neg);
        let nu = crt.mul(ac, &lambda, &acc.x, &[], &[&acc.y]);
        let u1 = crt.mul(ac, &lambda, p1.x(), &[], &[]);
        let u0 = crt.mul(ac, &nu, p1.y(), &[], &[]);
        self.e6_mul_sparse(ac, f, &u0, &u1);
        acc.x = acc2.x;
        acc.y = acc2.y;
    }

    #[allow(clippy::too_many_arguments)]
    fn add_eval_fixed(
        &self,
        ac: &mut AbstractCircuit<N>,
        f: &mut E6<VarBig<N>>,
        acc: &mut Point<BigUint>,
        p2: &Point<BigUint>,
        p1: &Point<VarBig<N>>,
        neg: bool,
        endo: bool,
    ) {
        let (lambda, nu) = Pairing::add(acc, p2, neg, endo);
        let lambda = self.base_field_crt.rns().big_from_uint(&lambda);
        let nu = self.base_field_crt.rns().big_from_uint(&nu);
        let u1 = self
            .base_field_crt
            .mul_constant(ac, p1.x(), &lambda, &[], &[]);
        let u0 = self.base_field_crt.mul_constant(ac, p1.y(), &nu, &[], &[]);
        self.e6_mul_sparse(ac, f, &u0, &u1);
    }

    fn endo(&self, ac: &mut AbstractCircuit<N>, p: &Point<VarBig<N>>) -> Point<VarBig<N>> {
        let x = self
            .base_field_crt
            .mul_constant(ac, p.x(), &self.zeta, &[], &[]);
        let y = self.base_field_crt.neg(ac, p.y());
        Point::new(x, y)
    }

    pub fn pairing_check_mixed(
        &self,
        ac: &mut AbstractCircuit<N>,
        p1_var: &[Point<VarBig<N>>],
        p2_var: &[Point<VarBig<N>>],
        p1_fix: &[Point<VarBig<N>>],
        p2_fix: &[Point<BigUint>],
    ) -> Result<(), Error> {
        let c = {
            let p1: Value<Vec<_>> =
                Value::from_iter(p1_var.iter().chain(p1_fix).map(|p1| p1.transpose()));
            let p2_var: Value<Vec<_>> = Value::from_iter(p2_var.iter().map(|p2| p2.transpose()));
            p1.zip(p2_var).map(|(p1, p2_var)| {
                let p2 = p2_var.iter().chain(p2_fix).cloned().collect_vec();
                Pairing::final_exp_witness(&p1, &p2)
            })
        };

        // Prepare for simpler line equation
        let p1_var = self.prepare_point(ac, p1_var);
        let p1_fix = self.prepare_point(ac, p1_fix);

        let c = self.e6_assign(ac, c)?;
        let c_inv = self.e6_inverse(ac, &c)?;
        let cq = self.e6_frobenius_map(ac, &c);
        let cq_inv = self.e6_frobenius_map(ac, &c_inv);

        let mut f = cq_inv.clone();

        let p2_var_endo = p2_var
            .iter()
            .map(|p2| self.endo(ac, p2))
            .collect::<Vec<_>>();

        let mut acc_var = p2_var_endo.to_vec();
        let mut acc_fix = Pairing::endo(p2_fix);

        for (x2, x1) in LOOP_2_NAF
            .iter()
            .skip(1)
            .rev()
            .skip(1)
            .zip(LOOP_1_NAF.iter().skip(1).rev().skip(1))
        {
            let x = x2 * 3 + x1;

            // f = self.e6_reduce(ac, &f);
            f = self.e6_square(ac, &f);

            p1_var
                .iter()
                .zip(acc_var.iter_mut())
                .for_each(|(p1, acc)| self.double_eval(ac, &mut f, acc, p1));

            p1_fix
                .iter()
                .zip(acc_fix.iter_mut())
                .for_each(|(p1, acc)| self.double_eval_fixed(ac, &mut f, acc, p1));

            match x {
                -3 => {
                    f = self.e6_mul(ac, &f, &cq);
                    p1_var
                        .iter()
                        .zip(p2_var_endo.iter())
                        .zip(acc_var.iter_mut())
                        .for_each(|((p1, p2), acc)| self.add_eval(ac, &mut f, acc, p2, p1, true));
                    p1_fix
                        .iter()
                        .zip(p2_fix.iter())
                        .zip(acc_fix.iter_mut())
                        .for_each(|((p1, p2), acc)| {
                            self.add_eval_fixed(ac, &mut f, acc, p2, p1, true, true)
                        });
                }
                -1 => {
                    f = self.e6_mul(ac, &f, &c);
                    p1_var
                        .iter()
                        .zip(p2_var.iter())
                        .zip(acc_var.iter_mut())
                        .for_each(|((p1, p2), acc)| self.add_eval(ac, &mut f, acc, p2, p1, true));
                    p1_fix
                        .iter()
                        .zip(p2_fix.iter())
                        .zip(acc_fix.iter_mut())
                        .for_each(|((p1, p2), acc)| {
                            self.add_eval_fixed(ac, &mut f, acc, p2, p1, true, false)
                        });
                }
                1 => {
                    f = self.e6_mul(ac, &f, &c_inv);
                    p1_var
                        .iter()
                        .zip(p2_var.iter())
                        .zip(acc_var.iter_mut())
                        .for_each(|((p1, p2), acc)| self.add_eval(ac, &mut f, acc, p2, p1, false));
                    p1_fix
                        .iter()
                        .zip(p2_fix.iter())
                        .zip(acc_fix.iter_mut())
                        .for_each(|((p1, p2), acc)| {
                            self.add_eval_fixed(ac, &mut f, acc, p2, p1, false, false)
                        });
                }
                3 => {
                    f = self.e6_mul(ac, &f, &cq_inv);
                    p1_var
                        .iter()
                        .zip(p2_var_endo.iter())
                        .zip(acc_var.iter_mut())
                        .for_each(|((p1, p2), acc)| self.add_eval(ac, &mut f, acc, p2, p1, false));
                    p1_fix
                        .iter()
                        .zip(p2_fix.iter())
                        .zip(acc_fix.iter_mut())
                        .for_each(|((p1, p2), acc)| {
                            self.add_eval_fixed(ac, &mut f, acc, p2, p1, false, true)
                        });
                }
                _ => {}
            }
        }

        f = self.e6_square(ac, &f);

        p1_var
            .iter()
            .zip(acc_var.iter_mut())
            .for_each(|(p1, acc)| self.double_eval(ac, &mut f, acc, p1));
        p1_fix
            .iter()
            .zip(acc_fix.iter_mut())
            .for_each(|(p1, acc)| self.double_eval_fixed(ac, &mut f, acc, p1));

        f = self.e6_mul(ac, &f, &cq);
        let one = self.e6_one(ac);
        let must_be_zero = self.e6_sub(ac, &f, &one);
        self.e6_assert_zero(ac, &must_be_zero)?;

        Ok(())
    }

    pub fn pairing_check(
        &self,
        ac: &mut AbstractCircuit<N>,
        p1: &[Point<VarBig<N>>],
        p2: &[Point<VarBig<N>>],
    ) -> Result<(), Error> {
        self.pairing_check_mixed(ac, p1, p2, &[], &[])
    }
}
