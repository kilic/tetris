use super::{LayoutCtx, RegionCtx};
use crate::{
    ir::mem::{Entry, MemWriteOnceIR, Query},
    witness::Var,
};
use halo2_proofs::{
    circuit::Layouter,
    halo2curves::ff::PrimeField,
    plonk::ErrorFront,
    plonk::{Advice, Column, ConstraintSystem, Fixed, Selector},
    poly::Rotation,
};

// dynamic lookup gate with the rules below:
// indicate witness in paranthesis as `(some_witness)`
// `address == query_coarse + (query_fine)`
// `memory_segment == query_segment`
// `[(t0), (t1), ...] == [(q0), (q1), ...]`

// gate allows multiple valid entries for same memory address
// however in synth time it can be constrained to point single
// vector of entries

#[derive(Clone, Debug)]
pub struct MemWriteOnceGate {
    pub(crate) query_selector: Selector,

    // coarse tuning of the query address
    // enforce the scale of the query address
    pub(crate) query_coarse: Column<Fixed>,
    // fine tuning of the query address
    // better to fit in a range
    pub(crate) query_fine: Column<Advice>,
    // fix the adress of written values
    pub(crate) address: Column<Fixed>,
    // to use same memory space for multiple pages
    pub(crate) segment: Column<Fixed>,
    // written and read values goes to the same columns
    pub(crate) table: Vec<Column<Advice>>,
}

impl MemWriteOnceGate {
    pub fn configure<F: PrimeField>(
        meta: &mut ConstraintSystem<F>,
        query_fine: Column<Advice>,
        table: &[Column<Advice>],
    ) -> Self {
        assert!(!table.is_empty());

        let segment = meta.fixed_column();

        let address = meta.fixed_column();
        let query_coarse = meta.fixed_column();
        let query_selector = meta.complex_selector();

        meta.enable_equality(query_fine);
        table.iter().for_each(|e| meta.enable_equality(*e));

        meta.lookup_any("write once memory", |meta| {
            let query_selector = meta.query_selector(query_selector);
            let segment = meta.query_fixed(segment, Rotation::cur());

            let address = meta.query_fixed(address, Rotation::cur());
            let table: Vec<_> = table
                .iter()
                .map(|table| meta.query_advice(*table, Rotation::cur()))
                .collect();

            let query_fine = meta.query_advice(query_fine, Rotation::cur());
            let query_coarse = meta.query_fixed(query_coarse, Rotation::cur());

            let query = std::iter::empty()
                .chain(table.clone())
                .chain(std::iter::once(query_fine + query_coarse))
                .chain(std::iter::once(segment.clone()));

            let memory = std::iter::empty()
                .chain(table.clone())
                .chain(std::iter::once(address))
                .chain(std::iter::once(segment));

            query
                .into_iter()
                .zip(memory)
                .map(|(query, table)| (query_selector.clone() * query, table))
                .collect::<Vec<_>>()
        });

        Self {
            query_selector,
            segment,
            query_coarse,
            query_fine,
            address,
            table: table.to_vec(),
        }
    }
}

impl MemWriteOnceGate {
    pub fn layout<F: PrimeField + Ord, L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: &MemWriteOnceIR<F>,
    ) -> Result<(), ErrorFront> {
        #[cfg(feature = "inspect")]
        {
            println!("---------");
            println!("MemWriteOnceGate::layout");
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut RegionCtx::new(region, &mut ly_ctx.cell_map);

                for Entry {
                    segment,
                    address,
                    values,
                } in e.entries.iter()
                {
                    self.write(ctx, *segment, *address, values)?;
                }
                Ok(ctx.offset())
            },
        )?;

        #[cfg(feature = "inspect")]
        {
            println!("* rows write: {_offset}");
            println!();
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut RegionCtx::new(region, &mut ly_ctx.cell_map);

                for Query {
                    segment,
                    address_offset,
                    address_fine,
                    values,
                } in e.queries.iter()
                {
                    self.read(ctx, *segment, *address_offset, address_fine, values)?;
                }
                Ok(ctx.offset())
            },
        )?;

        #[cfg(feature = "inspect")]
        {
            println!("* rows read: {_offset}");
            println!();
        }

        Ok(())
    }
}

impl MemWriteOnceGate {
    fn read<F: PrimeField + Ord>(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        segment: F,
        address_offset: F,
        address_fine: &Var<F>,
        values: &[Var<F>],
    ) -> Result<(), ErrorFront> {
        assert_eq!(values.len(), self.table.len());
        values
            .iter()
            .zip(self.table.iter())
            .try_for_each(|(limb, column)| ctx.advice(*column, limb))?;
        ctx.fixed(self.segment, segment)?;
        ctx.fixed(self.query_coarse, address_offset)?;
        ctx.advice(self.query_fine, address_fine)?;
        ctx.empty(self.address.into())?;
        ctx.enable(self.query_selector)?;
        ctx.next();
        Ok(())
    }

    fn write<F: PrimeField + Ord>(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        segment: F,
        address: F,
        values: &[Var<F>],
    ) -> Result<(), ErrorFront> {
        assert_eq!(values.len(), self.table.len());
        values
            .iter()
            .zip(self.table.iter())
            .try_for_each(|(limb, column)| ctx.advice(*column, limb))?;

        ctx.fixed(self.segment, segment)?;
        ctx.fixed(self.address, address)?;
        ctx.next();
        Ok(())
    }
}
