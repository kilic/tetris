use crate::ir::bitwise::Bitwise;

use super::{LayoutCtx, RegionCtx};
use halo2_proofs::{
    circuit::{Layouter, Value},
    halo2curves::ff::PrimeField,
    plonk::{Advice, Column, ConstraintSystem, ErrorFront, Selector, TableColumn},
    poly::Rotation,
};

#[derive(Clone, Debug)]
pub struct BitwiseGate {
    pub(crate) selector: Selector,
    pub(crate) v0: Column<Advice>,
    pub(crate) v1: Column<Advice>,
    pub(crate) res: Column<Advice>,
    pub(crate) tv0: TableColumn,
    pub(crate) tv1: TableColumn,
    pub(crate) tres: TableColumn,
    pub(crate) bit_size: usize,
}

impl BitwiseGate {
    pub fn configure<F: PrimeField>(
        meta: &mut ConstraintSystem<F>,
        advices: [Column<Advice>; 3],
        bit_size: usize,
    ) -> Self {
        let v0 = advices[0];
        let v1 = advices[1];
        let res = advices[2];
        let selector = meta.complex_selector();
        meta.enable_equality(v0);
        meta.enable_equality(v1);
        meta.enable_equality(res);
        let tv0 = meta.lookup_table_column();
        let tv1 = meta.lookup_table_column();
        let tres = meta.lookup_table_column();
        meta.lookup("xor", |meta| {
            let v0 = meta.query_advice(v0, Rotation::cur());
            let v1 = meta.query_advice(v1, Rotation::cur());
            let res = meta.query_advice(res, Rotation::cur());
            let s = meta.query_selector(selector);
            vec![
                (s.clone() * v0, tv0),
                (s.clone() * v1, tv1),
                (s * res, tres),
            ]
        });

        Self {
            selector,
            v0,
            v1,
            res,
            tv0,
            tv1,
            tres,
            bit_size,
        }
    }
}

impl BitwiseGate {
    pub fn layout_xor_table<F: PrimeField + Ord, L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
    ) -> Result<(), ErrorFront> {
        #[cfg(feature = "inspect")]
        {
            println!("---------");
            println!("BitwiseGate::layout_xor_table_{}", self.bit_size);
        }
        ly_ctx.layouter.assign_table(
            || "",
            |mut table| {
                let mut offset = 0;
                for v0 in 0u64..1 << self.bit_size {
                    for v1 in 0..1 << self.bit_size {
                        let res = v0 ^ v1;
                        table.assign_cell(
                            || "v0",
                            self.tv0,
                            offset,
                            || Value::known(F::from(v0)),
                        )?;
                        table.assign_cell(
                            || "v1",
                            self.tv1,
                            offset,
                            || Value::known(F::from(v1)),
                        )?;
                        table.assign_cell(
                            || "res",
                            self.tres,
                            offset,
                            || Value::known(F::from(res)),
                        )?;
                        offset += 1
                    }
                }
                Ok(())
            },
        )?;
        #[cfg(feature = "inspect")]
        println!();
        Ok(())
    }

    pub fn layout_and_table<F: PrimeField + Ord, L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
    ) -> Result<(), ErrorFront> {
        #[cfg(feature = "inspect")]
        {
            println!("---------");
            println!("BitwiseGate::layout_and_table_{}", self.bit_size);
        }
        ly_ctx.layouter.assign_table(
            || "",
            |mut table| {
                let mut offset = 0;
                for v0 in 0u64..1 << self.bit_size {
                    for v1 in 0..1 << self.bit_size {
                        let res = v0 & v1;

                        table.assign_cell(
                            || "v0",
                            self.tv0,
                            offset,
                            || Value::known(F::from(v0)),
                        )?;
                        table.assign_cell(
                            || "v1",
                            self.tv1,
                            offset,
                            || Value::known(F::from(v1)),
                        )?;
                        table.assign_cell(
                            || "res",
                            self.tres,
                            offset,
                            || Value::known(F::from(res)),
                        )?;
                        offset += 1
                    }
                }
                Ok(())
            },
        )?;
        #[cfg(feature = "inspect")]
        println!();
        Ok(())
    }

    pub fn layout<F: PrimeField + Ord, L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: &[Bitwise<F>],
    ) -> Result<(), ErrorFront> {
        #[cfg(feature = "inspect")]
        {
            println!("---------");
            println!("Bitwise::layout");
        }
        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut RegionCtx::new(region, &mut ly_ctx.cell_map);
                for op in e.iter() {
                    ctx.enable(self.selector)?;

                    ctx.advice(self.v0, &op.v0)?;
                    ctx.advice(self.v1, &op.v1)?;
                    ctx.advice(self.res, &op.res)?;
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
