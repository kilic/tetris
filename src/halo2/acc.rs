use super::{LayoutCtx, RegionCtx};
use crate::{
    ir::combination::{
        linear::{LcCoeff, LcVar},
        quad::{QcCoeff, QcVar},
    },
    Term, Value, Var,
};
use ark_std::{end_timer, start_timer};
use halo2_proofs::{
    circuit::Layouter,
    halo2curves::ff::PrimeField,
    plonk::{
        Advice, Challenge, Column, ConstraintSystem, Constraints, ErrorFront, Expression, Fixed,
        Selector,
    },
    poly::Rotation,
};
use itertools::{izip, Itertools};
use std::collections::BTreeMap;

#[derive(Clone, Debug)]
pub struct LinearAccGate {
    pub(crate) coeff: Column<Fixed>,
    pub(crate) constant: Column<Fixed>,
    pub(crate) advices: Vec<Column<Advice>>,
    pub(crate) acc: Column<Advice>,
    pub(crate) alpha: Challenge,

    pub(crate) selector: Selector,
    pub(crate) selector_zero: Selector,
}

#[derive(Clone, Debug)]
pub struct QuadAccGate {
    pub(crate) coeff: Column<Fixed>,
    pub(crate) constant: Column<Fixed>,
    pub(crate) advices: Vec<Column<Advice>>,
    pub(crate) acc: Column<Advice>,
    pub(crate) alpha: Challenge,

    pub(crate) selector_lin: Selector,
    pub(crate) selector_quad: Selector,
    pub(crate) selector_zero: Selector,
    pub(crate) selector_relay: Selector,
}

fn zero_gate<F: PrimeField>(meta: &mut ConstraintSystem<F>, acc: &Column<Advice>) -> Selector {
    let selector = meta.selector();

    // Or we could add acc column to copy argument?
    meta.create_gate("zero", |meta| {
        let selector = meta.query_selector(selector);
        let acc = meta.query_advice(*acc, Rotation::cur());
        Constraints::with_selector(selector, std::iter::once(acc))
    });

    selector
}

fn relay_gate<F: PrimeField>(meta: &mut ConstraintSystem<F>, acc: &Column<Advice>) -> Selector {
    let selector = meta.selector();

    // Or we could add acc column to copy argument?
    meta.create_gate("relay", |meta| {
        let selector = meta.query_selector(selector);
        let acc_prev = meta.query_advice(*acc, Rotation::prev());
        let acc = meta.query_advice(*acc, Rotation::cur());
        Constraints::with_selector(selector, std::iter::once(acc - acc_prev))
    });

    selector
}

fn linear_gate<F: PrimeField>(
    meta: &mut ConstraintSystem<F>,
    coeff: &Column<Fixed>,
    advices: &[Column<Advice>],
    constant: &Column<Fixed>,
    alpha: Challenge,
    acc: &Column<Advice>,
) -> Selector {
    let selector = meta.selector();
    advices.iter().for_each(|e| meta.enable_equality(*e));

    meta.create_gate("combine linear", |meta| {
        // `a = a_0 * F_0 + a_1 * F_1 + ... + constant`
        // `b = b_0 * F_0 + b_1 * F_1 + ... + constant`
        //
        // |                             | Fixed     | A    | B    | ACC                                            | constant | ACC == 0 |
        // | --------------------------- | --------- | ---- | ---- | ---------------------------------------------- | -------- | -------- |
        // | End of previous combination | ..        | ..   | ..   | `0`                                            | `0`      | `1`      |
        // | Rlc 0th terms               | F0        | `a0` | `b0` | `acc0 = F0 * (a0 + α * b0)`                    | `0`      | `0`      |
        // | Rlc 1st terms               | F1        | `a1` | `b1` | `acc1 = F1 * (a1 + α * b1) + acc0`             | `0`      | `0`      |
        // | Rlc 2nd terms               | F2        | `a2` | `b2` | `acc2 = F2 * (a2 + α * b2) + acc1`             | `0`      | `0`      |
        // | End. ACC is enfoced to be 0 | F3 = `-1` | `a`  | `b`  | `acc3 = F3 * (a + α * b) + acc2 + C * (1 + α)` | `c`      | `1`      |
        // | Next bunch of combinations  | ..        | ..   | ..   | `acc0 = ..`                                    | `0`      | `0`      |

        // to rlc bunch of columns
        let alpha = meta.query_challenge(alpha);

        let advices = advices
            .iter()
            .map(|advice| meta.query_advice(*advice, Rotation::cur()))
            .collect_vec();

        // rlc-ed columns
        let init = advices.first().unwrap().clone();
        let rlc_column = advices
            .iter()
            .skip(1)
            .fold(init, |acc, next| acc * alpha.clone() + next.clone());
        // scale with common coeff `F_i`
        // `rlc_column = F_i * (a_i + α * b_i + α^2 * c_i + ...)`
        let coeff = meta.query_fixed(*coeff, Rotation::cur());
        let rlc_column = rlc_column * coeff.clone();

        // we want to add a constant term to add to a combination
        let constant = meta.query_fixed(*constant, Rotation::cur());
        let rlc_alpha = advices
            .iter()
            .skip(1)
            .fold(Expression::Constant(F::ONE), |acc, _| {
                acc * alpha.clone() + Expression::Constant(F::ONE)
            });

        // `constant * (1 + α + α^2 + ...)`
        let rlc_constant = rlc_alpha * constant.clone();

        // note that in a combination ideally we want to activate constant only once
        // `rlc_column = F_i * (a_i + α * b_i + α^2 * c_i + ...) + C * (1 + α + α^2 + ...)`
        let rlc_column = rlc_column + rlc_constant;

        let acc_prev = meta.query_advice(*acc, Rotation::prev());
        let acc = meta.query_advice(*acc, Rotation::cur());

        let linear_acc_gate = acc_prev + rlc_column - acc;
        let selector = meta.query_selector(selector);
        Constraints::with_selector(selector, std::iter::once(linear_acc_gate))
    });

    selector
}

fn quad_gate<F: PrimeField>(
    meta: &mut ConstraintSystem<F>,
    coeff: &Column<Fixed>,
    advices: &[Column<Advice>],
    constant: &Column<Fixed>,
    alpha: Challenge,
    acc: &Column<Advice>,
) -> Selector {
    let selector = meta.selector();
    advices.iter().for_each(|e| meta.enable_equality(*e));

    meta.create_gate("combine quadratic", |meta| {
        // as in example below it can be combined with linear combination as well

        // |                                        | Fixed | A     | B     | ACC                                      | constant | ACC == 0 | ACC_(i-1) == ACC |
        // | -------------------------------------- | ----- | ----- | ----- | ---------------------------------------- | -------- | -------- | ---------------- |
        // | End of previous combination            | ..    | ..    | ..    | `0`                                      | `0`      | `1`      | `0`              |
        // | Lhs of 0th quad terms, ACC relayed     | n/a   | `al0` | `bl0` | `0`                                      | `0`      | `0`      | `1`              |
        // | Rhs of 0th quad terms, ACC accumulated | F0    | `ar0` | `br0` | `acc0 = F0 * (amul0 + α * bmul1) + acc0` | `0`      | `0`      | `0`              |
        // | Lhs of 1th quad terms, ACC relayed     | n/a   | `al1` | `bl1` | `acc0`                                   | `0`      | `0`      | `1`              |
        // | Rhs of 1th quad terms, ACC accumulated | F1    | `ar1` | `br1` | `acc1 = F0 * (amul1 + α * bmul1) + acc0` | `0`      | `0`      | `0`              |
        // | Rlc 0th linear terms                   | F2    | `a0`  | `b0`  | `acc2 = F2 * (a0 + α * b0) + acc1`       | `0`      | `0`      | `0`              |
        // | Rlc 1st linear terms                   | F3    | `a1`  | `b1`  | `acc3 = F3 * (a1 + α * b1) + acc2`       | `0`      | `0`      | `0`              |
        // | ..                                     | ..    | ..    | ..    | ..                                       | ..       | ..       | ..               |

        // rlc challange
        let alpha = meta.query_challenge(alpha);

        // lhs operand of the multiplication
        let lhs = advices
            .iter()
            .map(|advice| meta.query_advice(*advice, Rotation::prev()))
            .collect_vec();

        // rhs operand of the multiplication
        let rhs = advices
            .iter()
            .map(|advice| meta.query_advice(*advice, Rotation::cur()))
            .collect_vec();

        let init = lhs.first().unwrap().clone() * rhs.first().unwrap().clone();
        let rlc_column = lhs
            .iter()
            .zip(rhs.iter())
            .skip(1)
            .fold(init, |acc, (lhs, rhs)| {
                acc * alpha.clone() + lhs.clone() * rhs.clone()
            });
        // `rlc_column = F_i * (al_i * ar_i + α * bl_i * br_i + α^2 * cl_i * cr_i + ...)`
        let coeff = meta.query_fixed(*coeff, Rotation::cur());
        let rlc_column = rlc_column * coeff.clone();

        // we want to add a constant term to add to a combination
        let constant = meta.query_fixed(*constant, Rotation::cur());
        let rlc_alpha = advices
            .iter()
            .skip(1)
            .fold(Expression::Constant(F::ONE), |acc, _| {
                acc * alpha.clone() + Expression::Constant(F::ONE)
            });

        // `rlc_constant = constant * (1 + α + α^2 + ...)`
        let rlc_constant = rlc_alpha * constant.clone();

        // note that in a combination ideally we want to activate constant only once
        // `rlc_column = F_i * (al_i * ar_i + α * bl_i * br_i + α^2 * cl_i * cr_i + ...) + constant * (1 + α + α^2 + ...)`
        let rlc_column = rlc_column + rlc_constant;

        let acc_prev = meta.query_advice(*acc, Rotation::prev());
        let acc = meta.query_advice(*acc, Rotation::cur());

        let quad_acc_gate = acc_prev + rlc_column - acc;
        let selector = meta.query_selector(selector);
        Constraints::with_selector(selector, std::iter::once(quad_acc_gate))
    });

    selector
}

impl LinearAccGate {
    pub fn configure<F: PrimeField>(
        meta: &mut ConstraintSystem<F>,
        coeff: &Column<Fixed>,
        advices: &[Column<Advice>],
        constant: &Column<Fixed>,
        alpha: Challenge,
        acc: &Column<Advice>,
    ) -> Self {
        let selector = linear_gate(meta, coeff, advices, constant, alpha, acc);
        let selector_zero = zero_gate(meta, acc);
        LinearAccGate {
            coeff: *coeff,
            advices: advices.to_vec(),
            constant: *constant,
            alpha,
            acc: *acc,
            selector,
            selector_zero,
        }
    }
}

impl QuadAccGate {
    pub fn configure<F: PrimeField>(
        meta: &mut ConstraintSystem<F>,
        coeff: &Column<Fixed>,
        advices: &[Column<Advice>],
        constant: &Column<Fixed>,
        alpha: Challenge,
        acc: &Column<Advice>,
    ) -> Self {
        let selector_lin = linear_gate(meta, coeff, advices, constant, alpha, acc);
        let selector_quad = quad_gate(meta, coeff, advices, constant, alpha, acc);
        let selector_zero = zero_gate(meta, acc);
        let selector_relay = relay_gate(meta, acc);
        QuadAccGate {
            coeff: *coeff,
            advices: advices.to_vec(),
            constant: *constant,
            alpha,
            acc: *acc,
            selector_lin,
            selector_quad,
            selector_zero,
            selector_relay,
        }
    }

    pub fn linear_gate(&self) -> LinearAccGate {
        LinearAccGate {
            coeff: self.coeff,
            advices: self.advices.clone(),
            constant: self.constant,
            alpha: self.alpha,
            acc: self.acc,
            selector: self.selector_lin,
            selector_zero: self.selector_zero,
        }
    }
}

impl LinearAccGate {
    pub(crate) fn empty_row<F: PrimeField + Ord>(
        &self,
        ctx: &mut RegionCtx<F>,
    ) -> Result<(), ErrorFront> {
        ctx.empty(self.acc.into())?;
        self.advices
            .iter()
            .try_for_each(|advice| ctx.empty((*advice).into()))?;
        ctx.empty(self.coeff.into())?;
        ctx.empty(self.constant.into())?;
        ctx.enable(self.selector_zero)?;
        ctx.next();
        Ok(())
    }

    pub fn layout<F: PrimeField + Ord, L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: &BTreeMap<LcCoeff<F>, Vec<LcVar<F>>>,
    ) -> Result<(), ErrorFront> {
        #[cfg(feature = "inspect")]
        {
            println!("---------");
            println!("LinearAccGate::layout");
        }
        let timer = start_timer!(|| "LinearAccGate::layout");

        let n_columns = self.advices.len();
        let alpha: Value<F> = ly_ctx.layouter.get_challenge(self.alpha).into();
        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region: halo2_proofs::circuit::Region<_>| {
                let ctx = &mut RegionCtx::new(region, &mut ly_ctx.cell_map);

                // leave the very first row empty
                // to escape from cycleflow
                self.empty_row(ctx)?;

                for (LcCoeff { coeffs, constant }, vars) in e.iter() {
                    let n_rows = coeffs.len();
                    let dummy = &vars.first().unwrap()[..];

                    for chunk_of_vars in vars.chunks(n_columns) {
                        let chunk_of_vars = chunk_of_vars
                            .iter()
                            .map(Vec::as_slice)
                            .chain(std::iter::repeat(dummy))
                            .take(n_columns)
                            .collect_vec();
                        let chunk_of_vars = crate::utils::transpose(&chunk_of_vars);

                        // init rlc accumulator
                        let mut acc = Value::new(F::ZERO);

                        coeffs
                            .iter()
                            .zip(chunk_of_vars.iter())
                            .enumerate()
                            .try_for_each(|(i, (coeff, vars))| {
                                let constant = (i == n_rows - 1).then_some(*constant);
                                self.layout_row(ctx, &mut acc, *coeff, vars, &alpha, constant)
                            })?;
                    }
                }
                Ok(ctx.offset())
            },
        )?;

        end_timer!(timer);
        #[cfg(feature = "inspect")]
        {
            println!("* rows: {_offset}");
            println!();
        }

        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn layout_row<F: PrimeField + Ord>(
        &self,
        ctx: &mut RegionCtx<F>,
        acc: &mut Value<F>,
        coeff: F,
        terms: &[&Var<F>],
        alpha: &Value<F>,
        constant: Option<F>,
    ) -> Result<(), ErrorFront> {
        assert_eq!(self.advices.len(), terms.len());

        // assign the common fixed value
        ctx.fixed(self.coeff, coeff)?;

        // init row rlc accumulator
        let mut row_rlc = Value::new(F::ZERO);

        let is_last_row = constant.is_some();
        let constant = constant.unwrap_or(F::ZERO);

        for (term, column) in terms.iter().zip(self.advices.iter()) {
            // get the var part of term in the vertical axis and assign
            ctx.advice(*column, term)?;

            // term = coeff * term_var
            // and contibute the constant in the last row
            let term = term.value().map(|w| w * coeff + constant);

            // simply apply Horner
            row_rlc = row_rlc * alpha + term;
        }

        // add row rlc to the vertical accumulator
        *acc = *acc + row_rlc;
        // no copy is needed for intermediate value of accumulator
        ctx.advice_temp(self.acc, &acc.halo2())?;
        // open the accumulator
        ctx.enable(self.selector)?;

        if is_last_row {
            // feed the constant term in the last row
            ctx.fixed(self.constant, constant)?;

            // accumulator must arrive to zero at last row
            ctx.enable(self.selector_zero)?;

            acc.maybe(|acc| (acc == &F::ZERO).then_some(()))
                .map_err(|_| ErrorFront::Synthesis)?;
        } else {
            // constant term is zero at intermediate rows
            ctx.empty(self.constant.into())?;
        }

        // move to the next term
        ctx.next();
        Ok(())
    }
}

impl QuadAccGate {
    pub fn layout<F: PrimeField + Ord, L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: &BTreeMap<QcCoeff<F>, Vec<QcVar<F>>>,
    ) -> Result<(), ErrorFront> {
        #[cfg(feature = "inspect")]
        {
            println!("---------");
            println!("QuadAccGate::layout");
        }
        let timer = start_timer!(|| "QuadAccGate::layout");
        let n_columns = self.advices.len();
        let alpha = ly_ctx.layouter.get_challenge(self.alpha).into();

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region: halo2_proofs::circuit::Region<_>| {
                let ctx = &mut RegionCtx::new(region, &mut ly_ctx.cell_map);

                // leave the very first row empty
                // to escape from cycleflow
                self.linear_gate().empty_row(ctx)?;

                for (
                    QcCoeff {
                        lin: lin_coeffs,
                        quad: quad_coeffs,
                        constant,
                    },
                    terms,
                ) in e.iter()
                {
                    let n_lin = lin_coeffs.len();
                    let n_quad = quad_coeffs.len();
                    let dummy = terms.first().unwrap();

                    for chunk_of_vars in terms.chunks(n_columns) {
                        // check if all combinations matches with number of coeffs
                        #[cfg(feature = "synth-sanity")]
                        chunk_of_vars.iter().for_each(|c| {
                            assert_eq!(c.lin.len(), n_lin);
                            assert_eq!(c.quad.len(), n_quad);
                        });

                        let chunk_of_vars = chunk_of_vars
                            .iter()
                            .chain(std::iter::repeat(dummy))
                            .take(n_columns)
                            .cloned()
                            .collect_vec();

                        // init rlc accumulator
                        let mut acc = Value::new(F::ZERO);

                        // iterate over the terms of the chunk
                        for i_quad_term in 0..n_quad {
                            let is_last_row = i_quad_term == n_quad - 1 && n_lin == 0;

                            // assign the common fixed value
                            let coeff = quad_coeffs.get(i_quad_term).unwrap();

                            // init row rlc accumulator
                            let mut row_rlc = Value::new(F::ZERO);

                            for (combination, column) in
                                chunk_of_vars.iter().zip(self.advices.iter())
                            {
                                // get the var part of the term in vertical axis
                                let term = combination.quad.get(i_quad_term).unwrap();
                                {
                                    // - assign lhs of the quad var
                                    // - move one vertical step
                                    // - assign rhs of the quad var
                                    // - and get back to the previous vertical row

                                    ctx.advice(*column, &term.var0)?;
                                    ctx.empty(self.coeff.into())?;
                                    ctx.next();

                                    ctx.advice(*column, &term.var1)?;
                                    ctx.fixed(self.coeff, *coeff)?;
                                    ctx.prev();
                                }

                                // term = coeff * term_var
                                // and contibute the constant in the last row
                                let term = term.value().map(|w| {
                                    w * coeff + if is_last_row { *constant } else { F::ZERO }
                                });

                                // simply apply Horner
                                row_rlc = row_rlc * alpha + term;
                            }

                            // relay the accumulator
                            // no copy is needed for intermediate value of accumulator
                            ctx.enable(self.selector_relay)?;
                            ctx.advice_temp(self.acc, &acc.halo2())?;

                            // move to the next row
                            ctx.next();

                            // add row rlc to the vertical accumulator
                            acc = acc + row_rlc;
                            // open the accumulator
                            ctx.enable(self.selector_quad)?;
                            // assign the accumulator
                            // no copy is needed for intermediate value of accumulator
                            ctx.advice_temp(self.acc, &acc.halo2())?;

                            // expect zero at the last accumulator
                            if is_last_row {
                                // feed the constant term in the last row
                                ctx.fixed(self.constant, *constant)?;

                                // accumulator must arrive to zero at last
                                ctx.enable(self.selector_zero)?;

                                // let's also check in the prover time
                                // TODO: layout sanity
                                // #[cfg(feature = "prover-sanity")]
                                // acc.maybe(|acc| {
                                //     prover_sanity(
                                //         (*acc == F::ZERO).then_some(()),
                                //         "cannot recover point",
                                //     )
                                // })
                                // .map_err(|_| Error::Synthesis)?;
                            } else {
                                // constant term is zero at intermediate rows
                                ctx.empty(self.constant.into())?;
                            }

                            // move to the next term
                            ctx.next();
                        }

                        let lin_part = chunk_of_vars.iter().map(|c| c.lin.as_slice()).collect_vec();
                        let lin_part = crate::utils::transpose(&lin_part);

                        izip!(lin_coeffs, lin_part).enumerate().try_for_each(
                            |(i, (coeff, vars))| {
                                let constant = (i == n_lin - 1).then_some(*constant);
                                self.linear_gate()
                                    .layout_row(ctx, &mut acc, *coeff, &vars, &alpha, constant)
                            },
                        )?;
                    }
                }
                Ok(ctx.offset())
            },
        )?;

        end_timer!(timer);
        #[cfg(feature = "inspect")]
        {
            println!("* rows: {_offset}");
            println!();
        }

        Ok(())
    }
}
