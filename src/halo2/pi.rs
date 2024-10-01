use super::{LayoutCtx, RegionCtx};
use crate::Var;
use halo2_proofs::{
    circuit::Layouter,
    halo2curves::ff::PrimeField,
    plonk::{Advice, Column, ConstraintSystem, Constraints, ErrorFront, Selector},
    poly::Rotation,
};

#[derive(Clone, Debug)]
pub struct PIGate {
    pub(crate) selector: Selector,
    pub(crate) advice: Column<Advice>,
}

impl PIGate {
    #[allow(clippy::too_many_arguments)]
    pub fn configure<F: PrimeField>(
        meta: &mut ConstraintSystem<F>,
        advice: Column<Advice>,
    ) -> Self {
        let selector = meta.selector();
        meta.enable_equality(advice);
        let pi = meta.instance_column();
        meta.create_gate("public input", |meta| {
            let advice = meta.query_advice(advice, Rotation::cur());
            let selector = meta.query_selector(selector);
            let pi = meta.query_instance(pi, Rotation::cur());
            Constraints::with_selector(selector, vec![(advice - pi)])
        });

        Self { advice, selector }
    }
}

impl PIGate {
    pub fn layout<F: PrimeField + Ord, L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: &[Var<F>],
    ) -> Result<(), ErrorFront> {
        #[cfg(feature = "inspect")]
        {
            println!("---------");
            println!("PIGate::layout");
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut RegionCtx::new(region, &mut ly_ctx.cell_map);
                for w in e.iter() {
                    ctx.enable(self.selector)?;
                    ctx.advice(self.advice, w)?;
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
