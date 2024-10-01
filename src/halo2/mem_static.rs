use super::{LayoutCtx, RegionCtx};
use crate::ir::mem::{MemReadOnlyIR, Query};
use halo2_proofs::{
    circuit::Layouter,
    halo2curves::ff::PrimeField,
    plonk::{Advice, Column, ConstraintSystem, ErrorFront, Fixed, Selector},
    poly::Rotation,
};

#[derive(Clone, Debug)]
pub struct MemReadOnlyGate {
    pub(crate) selector: Selector,
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
    // values in table
    pub(crate) table_vector: Vec<Column<Fixed>>,
    // values in query
    pub(crate) query_vector: Vec<Column<Advice>>,
}

impl MemReadOnlyGate {
    pub fn configure<F: PrimeField>(
        meta: &mut ConstraintSystem<F>,
        query_fine: Column<Advice>,
        query_vector: &[Column<Advice>],
    ) -> Self {
        assert!(!query_vector.is_empty());

        let segment = meta.fixed_column();
        let address = meta.fixed_column();
        let query_coarse = meta.fixed_column();
        let selector = meta.complex_selector();

        let table_vector = query_vector
            .iter()
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>();

        meta.enable_equality(query_fine);
        query_vector.iter().for_each(|e| meta.enable_equality(*e));

        meta.lookup_any("read only memory", |meta| {
            let selector = meta.query_selector(selector);
            let segment = meta.query_fixed(segment, Rotation::cur());

            let address = meta.query_fixed(address, Rotation::cur());
            let query_vector: Vec<_> = query_vector
                .iter()
                .map(|e| meta.query_advice(*e, Rotation::cur()))
                .collect();
            let table_vector: Vec<_> = table_vector
                .iter()
                .map(|e| meta.query_fixed(*e, Rotation::cur()))
                .collect();

            let query_fine = meta.query_advice(query_fine, Rotation::cur());
            let query_coarse = meta.query_fixed(query_coarse, Rotation::cur());

            let query = std::iter::empty()
                .chain(query_vector.clone())
                .chain(std::iter::once(query_fine + query_coarse))
                .chain(std::iter::once(segment.clone()));

            let memory = std::iter::empty()
                .chain(table_vector.clone())
                .chain(std::iter::once(address))
                .chain(std::iter::once(segment));

            query
                .into_iter()
                .zip(memory)
                .map(|(query, table)| (selector.clone() * query, table))
                .collect::<Vec<_>>()
        });

        Self {
            selector,
            segment,
            query_coarse,
            query_fine,
            address,
            table_vector: table_vector.to_vec(),
            query_vector: query_vector.to_vec(),
        }
    }
}

impl MemReadOnlyGate {
    pub fn layout<F: PrimeField + Ord, L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: &MemReadOnlyIR<F>,
    ) -> Result<(), ErrorFront> {
        #[cfg(feature = "inspect")]
        {
            println!("---------");
            println!("MemReadOnlyGate::layout");
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut RegionCtx::new(region, &mut ly_ctx.cell_map);
                for ((segment, address), values) in e.table.iter() {
                    assert_eq!(values.len(), self.table_vector.len());

                    values
                        .iter()
                        .zip(self.table_vector.iter())
                        .try_for_each(|(e, column)| ctx.fixed(*column, *e))?;

                    ctx.fixed(self.segment, *segment)?;
                    ctx.fixed(self.address, *address)?;
                    ctx.next();
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
                    assert_eq!(values.len(), self.query_vector.len());

                    values
                        .iter()
                        .zip(self.query_vector.iter())
                        .try_for_each(|(e, column)| ctx.advice(*column, e))?;

                    ctx.fixed(self.segment, *segment)?;
                    ctx.fixed(self.query_coarse, *address_offset)?;
                    ctx.advice(self.query_fine, address_fine)?;
                    ctx.empty(self.address.into())?;
                    ctx.enable(self.selector)?;
                    ctx.next();
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
