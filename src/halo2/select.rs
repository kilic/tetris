use crate::ir::select::Select;

use super::{LayoutCtx, RegionCtx};
use halo2_proofs::{
    circuit::Layouter,
    halo2curves::ff::PrimeField,
    plonk::{Advice, Column, ConstraintSystem, Constraints, ErrorFront, Selector},
    poly::Rotation,
};

#[derive(Clone, Debug)]
pub struct SelectGate {
    pub(crate) selector: Selector,
    pub(crate) cond: Column<Advice>,
    pub(crate) w0: Column<Advice>,
    pub(crate) w1: Column<Advice>,
    pub(crate) selected: Column<Advice>,
}

impl SelectGate {
    #[allow(clippy::too_many_arguments)]
    pub fn configure<F: PrimeField>(
        meta: &mut ConstraintSystem<F>,
        advices: &[Column<Advice>; 4],
    ) -> Self {
        let selector = meta.selector();
        let cond = advices[0];
        let w0 = advices[1];
        let w1 = advices[2];
        let selected = advices[3];

        meta.create_gate("select", |meta| {
            let cond = meta.query_advice(cond, Rotation::cur());
            let w0 = meta.query_advice(w0, Rotation::cur());
            let w1 = meta.query_advice(w1, Rotation::cur());
            let selected = meta.query_advice(selected, Rotation::cur());
            let selector = meta.query_selector(selector);
            let expression = cond * (w1 - w0.clone()) + w0 - selected;
            Constraints::with_selector(selector, vec![expression])
        });

        Self {
            selector,
            cond,
            w0,
            w1,
            selected,
        }
    }
}

impl SelectGate {
    pub fn layout<F: PrimeField + Ord, L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: &[Select<F>],
    ) -> Result<(), ErrorFront> {
        #[cfg(feature = "inspect")]
        {
            println!("---------");
            println!("SelectGate::layout");
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut RegionCtx::new(region, &mut ly_ctx.cell_map);
                for op in e.iter() {
                    ctx.enable(self.selector)?;
                    let cond = op.cond;
                    let w0 = op.w0;
                    let w1 = op.w1;
                    let selected = op.selected;

                    ctx.advice(self.cond, &cond)?;
                    ctx.advice(self.w0, &w0)?;
                    ctx.advice(self.w1, &w1)?;
                    ctx.advice(self.selected, &selected)?;

                    ctx.next();
                }

                Ok(ctx.offset())
            },
        )?;

        #[cfg(feature = "inspect")]
        {
            println!("* rows: {_offset}");
            println!();
        }

        Ok(())
    }
}
