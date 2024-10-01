use super::acc::LinearAccGate;
use super::{LayoutCtx, RegionCtx};
use crate::ir::range::{RangeIR, RangeSingle, RcCoeff, RcVar};
use crate::utils;
use ark_std::{end_timer, start_timer};
use halo2_proofs::halo2curves::ff::PrimeField;
use halo2_proofs::poly::Rotation;
use halo2_proofs::{
    circuit::Layouter,
    plonk::{Column, ConstraintSystem, ErrorFront, Fixed, Selector, TableColumn},
};
use itertools::{izip, Itertools};
use std::collections::BTreeSet;

#[derive(Debug, Clone)]
pub struct RangeGate {
    pub(crate) selector: Selector,
    pub(crate) segment: Column<Fixed>,
    pub(crate) sign_shift: Column<Fixed>,
    pub(crate) value_table: TableColumn,
    pub(crate) segment_table: TableColumn,
    pub(crate) acc_gate: LinearAccGate,
}

impl RangeGate {
    pub fn configure<F: PrimeField>(
        meta: &mut ConstraintSystem<F>,
        acc_gate: LinearAccGate,
    ) -> RangeGate {
        let segment = meta.fixed_column();
        let sign_shift = meta.fixed_column();
        let selector = meta.complex_selector();
        let segment_table = meta.lookup_table_column();
        let value_table = meta.lookup_table_column();
        for advice in acc_gate.advices.iter() {
            meta.lookup("range", |meta| {
                let selector = meta.query_selector(selector);
                let advice = meta.query_advice(*advice, Rotation::cur());
                let segment = meta.query_fixed(segment, Rotation::cur());
                let sign_shift = meta.query_fixed(sign_shift, Rotation::cur());
                vec![
                    (segment, segment_table),
                    (selector * (advice + sign_shift), value_table),
                ]
            });
        }
        RangeGate {
            selector,
            sign_shift,
            segment_table,
            value_table,
            segment,
            acc_gate,
        }
    }

    pub fn enable<F: PrimeField + Ord>(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        size: usize,
        signed: bool,
    ) -> Result<(), ErrorFront> {
        ctx.enable(self.selector).unwrap();
        let segment = size + if signed { 2 } else { 1 };
        let segment = F::from(segment as u64);
        let sign_shift = if signed { 1 << size } else { 0 };
        let sign_shift = F::from(sign_shift as u64);
        ctx.fixed(self.segment, segment)?;
        ctx.fixed(self.sign_shift, sign_shift)?;
        Ok(())
    }

    pub fn layout_tables<F: PrimeField, L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        bit_sizes: &[usize],
    ) -> Result<(), ErrorFront> {
        let mut bit_sizes = bit_sizes.to_vec();
        bit_sizes.sort();
        if bit_sizes.is_empty() {
            return Ok(());
        }

        #[cfg(feature = "inspect")]
        {
            println!("---------");
            println!("RangeGate::layout_tables");
            println!("* bits: {:?}", bit_sizes);
            println!();
        }

        use halo2_proofs::circuit::Value;

        assert_ne!(*bit_sizes.first().unwrap(), 0);
        ly_ctx.layouter.assign_table(
            || "",
            |mut table| {
                let mut offset = 0;

                table.assign_cell(
                    || "table segment",
                    self.segment_table,
                    0,
                    || Value::known(F::ZERO),
                )?;
                table.assign_cell(
                    || "table value",
                    self.value_table,
                    0,
                    || Value::known(F::ZERO),
                )?;
                offset += 1;

                for bit_size in bit_sizes.iter() {
                    assert!(*bit_size < F::S as usize - 3);
                    let table_values: Vec<F> = (0..1 << *bit_size).map(|e| F::from(e)).collect();
                    for value in table_values.iter() {
                        table.assign_cell(
                            || "table segment",
                            self.segment_table,
                            offset,
                            || Value::known(F::from(*bit_size as u64 + 1)),
                        )?;
                        table.assign_cell(
                            || "table value",
                            self.value_table,
                            offset,
                            || Value::known(*value),
                        )?;
                        offset += 1;
                    }
                }
                Ok(())
            },
        )?;
        Ok(())
    }

    pub fn layout<F: PrimeField + Ord, L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        range_ir: &RangeIR<F>,
    ) -> Result<Vec<usize>, ErrorFront> {
        #[cfg(feature = "inspect")]
        {
            println!("---------");
            println!("RangeGate::layout");
        }
        let timer = start_timer!(|| "RangeGate::layout");

        let pow_of_twos = (0..F::NUM_BITS)
            .map(|i| F::from(2).pow([i as u64, 0, 0, 0]))
            .collect_vec();

        // we will collect bit size occurences
        let mut bit_sizes = BTreeSet::new();

        // number of range composition chunks are equal to the number of columns
        let acc_gate = &self.acc_gate;
        let n_columns = acc_gate.advices.len();

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region: halo2_proofs::circuit::Region<_>| {
                let ctx = &mut RegionCtx::new(region, &mut ly_ctx.cell_map);

                // leave the very first row empty
                // to escape from cycleflow
                acc_gate.empty_row(ctx)?;

                for (range, vars) in range_ir.singles.iter() {
                    let RangeSingle { size, signed } = *range;
                    // to fill the region get a dummy var
                    let dummy = vars.first().unwrap();
                    for chunk in vars.chunks(n_columns) {
                        // and fill the region
                        let chunk = chunk
                            .iter()
                            .chain(std::iter::repeat(dummy))
                            .take(n_columns)
                            .cloned()
                            .collect_vec();

                        // open the gate
                        self.enable(ctx, size, signed)?;
                        // collect the bit size occurences
                        bit_sizes.insert(size + if signed { 1 } else { 0 });

                        // layout the chunk
                        chunk
                            .iter()
                            .zip(acc_gate.advices.iter())
                            .try_for_each(|(var, column)| ctx.advice(*column, var))?;

                        // leave others at zero
                        ctx.empty(acc_gate.constant.into())?;
                        ctx.empty(acc_gate.coeff.into())?;
                        ctx.empty(acc_gate.acc.into())?;

                        ctx.next();
                    }
                }

                Ok(ctx.offset())
            },
        )?;

        #[cfg(feature = "inspect")]
        println!("* rows singles: {_offset}");

        let alpha = ly_ctx.layouter.get_challenge(acc_gate.alpha).into();
        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region: halo2_proofs::circuit::Region<_>| {
                let ctx = &mut RegionCtx::new(region, &mut ly_ctx.cell_map);

                // leave the very first row empty
                // to escape from cycleflow
                acc_gate.empty_row(ctx)?;

                for (coeff, vars) in range_ir.combinations.iter() {
                    let RcCoeff { sizes, signed } = coeff;
                    let n = sizes.len();

                    sizes.iter().for_each(|limb_size| {
                        assert_ne!(*limb_size, 0);
                        // collect the bit size occurences
                        bit_sizes.insert(limb_size + if *signed { 1 } else { 0 });
                    });

                    // check if all combinations matches with number of coeffs
                    vars.iter()
                        .for_each(|terms| assert_eq!(terms.limbs.len(), n));

                    // to fill the region get a dummy var
                    let dummy = vars.first().unwrap();

                    for chunk_of_terms in vars.chunks(n_columns) {
                        // and fill the region
                        let chunk_of_limbs = chunk_of_terms
                            .iter()
                            .map(RcVar::limbs)
                            .chain(std::iter::repeat(dummy).map(RcVar::limbs))
                            .take(n_columns)
                            .collect_vec();
                        let chunk_of_limbs = utils::transpose(&chunk_of_limbs);

                        // init rlc accumulator
                        let mut acc = crate::Value::new(F::ZERO);
                        let mut acc_size = 0;
                        for (size, row) in izip!(sizes, chunk_of_limbs) {
                            // get the base of the limb size
                            // TODO: fix this to signed?
                            let base = &pow_of_twos[acc_size];
                            // open the gate
                            self.enable(ctx, *size, *signed)?;
                            // layout current row
                            acc_gate.layout_row(ctx, &mut acc, *base, &row, &alpha, None)?;
                            // move power of two to the next limb
                            acc_size += *size;
                        }

                        let chunk_of_vars = chunk_of_terms
                            .iter()
                            .map(RcVar::var)
                            .chain(std::iter::repeat(dummy).map(RcVar::var))
                            .take(n_columns)
                            .collect_vec();

                        acc_gate.layout_row(
                            ctx,
                            &mut acc,
                            -F::ONE,
                            &chunk_of_vars,
                            &alpha,
                            Some(F::ZERO),
                        )?;
                    }
                }
                Ok(ctx.offset())
            },
        )?;

        end_timer!(timer);

        #[cfg(feature = "inspect")]
        {
            println!("* rows combinations: {_offset}");
            println!();
        }

        let mut bit_sizes = bit_sizes.iter().cloned().collect_vec();
        bit_sizes.sort();

        #[cfg(feature = "synth-sanity")]
        {
            let mut _bit_sizes = range_ir.sizes.iter().cloned().collect_vec();
            _bit_sizes.sort();
            assert_eq!(bit_sizes, _bit_sizes);
        }

        Ok(bit_sizes)
    }
}
