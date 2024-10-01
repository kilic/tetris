use crate::ir::pow5::Pow5;

use super::{LayoutCtx, RegionCtx};
use halo2_proofs::{
    circuit::Layouter,
    halo2curves::ff::PrimeField,
    plonk::{Advice, Column, ConstraintSystem, Constraints, ErrorFront, Selector},
    poly::Rotation,
};

#[derive(Clone, Debug)]
pub struct Pow5Gate {
    pub(crate) selector: Selector,
    pub(crate) w1: Column<Advice>,
    pub(crate) w5: Column<Advice>,
    pub(crate) w2: Column<Advice>,
    pub(crate) w3: Column<Advice>,
}

impl Pow5Gate {
    pub fn configure<F: PrimeField>(
        meta: &mut ConstraintSystem<F>,
        advices: &[Column<Advice>; 4],
    ) -> Self {
        let selector = meta.selector();
        let w1 = advices[0];
        let w5 = advices[1];
        let w2 = advices[2];
        let w3 = advices[3];
        meta.enable_equality(w1);
        meta.enable_equality(w5);

        meta.create_gate("pow5", |meta| {
            let w1 = meta.query_advice(w1, Rotation::cur());
            let w5 = meta.query_advice(w5, Rotation::cur());
            let w2 = meta.query_advice(w2, Rotation::cur());
            let w3 = meta.query_advice(w3, Rotation::cur());

            let e0 = w1.clone() * w1.clone() - w2.clone();
            let e1 = w1.clone() * w2.clone() - w3.clone();
            let e2 = w2.clone() * w3.clone() - w5.clone();

            let selector = meta.query_selector(selector);
            Constraints::with_selector(selector, vec![e0, e1, e2])
        });

        Self {
            selector,
            w1,
            w5,
            w2,
            w3,
        }
    }
}

impl Pow5Gate {
    pub fn layout<F: PrimeField + Ord, L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: &[Pow5<F>],
    ) -> Result<(), ErrorFront> {
        #[cfg(feature = "inspect")]
        {
            println!("---------");
            println!("Pow5Gate::layout");
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut RegionCtx::new(region, &mut ly_ctx.cell_map);

                for op in e.iter() {
                    ctx.enable(self.selector)?;

                    ctx.advice(self.w1, &op.w1)?;
                    ctx.advice(self.w5, &op.w5)?;
                    ctx.advice_temp(self.w2, &op.w2.halo2())?;
                    ctx.advice_temp(self.w3, &op.w3.halo2())?;
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

// Vertical option:

// #[derive(Clone, Debug)]
// pub struct Pow5Gate {
//     pub(crate) selector: Selector,
//     pub(crate) advices: Vec<Column<Advice>>,
// }

// impl Pow5Gate {
//     pub fn configure<F: PrimeField>(
//         meta: &mut ConstraintSystem<F>,
//         advices: &[Column<Advice>],
//     ) -> Self {
//         let selector = meta.selector();
//         advices
//             .iter()
//             .for_each(|advice| meta.enable_equality(*advice));

//         for advice in advices.iter() {
//             meta.create_gate("pow5", |meta| {
//                 let w = meta.query_advice(*advice, Rotation::cur());
//                 let w2 = meta.query_advice(*advice, Rotation(1));
//                 let w3 = meta.query_advice(*advice, Rotation(2));
//                 let w5 = meta.query_advice(*advice, Rotation(3));

//                 let e0 = w.clone() * w.clone() - w2.clone();
//                 let e1 = w.clone() * w2.clone() - w3.clone();
//                 let e2 = w2.clone() * w3.clone() - w5.clone();

//                 let selector = meta.query_selector(selector);
//                 Constraints::with_selector(selector, vec![e0, e1, e2])
//             });
//         }
//         Self {
//             selector,
//             advices: advices.to_vec(),
//         }
//     }
// }

// impl Pow5Gate {
//     pub fn layout<F: PrimeField + Ord, L: Layouter<F>>(
//         &self,
//         ly_ctx: &mut LayoutCtx<F, L>,
//         e: &[Pow5<F>],
//     ) -> Result<(), Error> {
//         #[cfg(feature = "inspect")]
//         {
//             println!("---------");
//             println!("Pow5Gate::layout");
//         }

//         let _offset = ly_ctx.layouter.assign_region(
//             || "",
//             |region| {
//                 let ctx = &mut RegionCtx::new(region, &mut ly_ctx.cell_map);

//                 for chunk in e.chunks(self.advices.len()) {
//                     ctx.enable(self.selector)?;
//                     for (op, advice) in chunk.iter().zip(self.advices.iter()) {
//                         let w = op.w;
//                         let w2 = op.w2;
//                         let w3 = op.w3;
//                         let w5 = op.w5;

//                         ctx.advice(*advice, &w)?;
//                         ctx.next();
//                         ctx.advice_temp(*advice, &w2.halo2())?;
//                         ctx.next();
//                         ctx.advice_temp(*advice, &w3.halo2())?;
//                         ctx.next();
//                         ctx.advice(*advice, &w5)?;
//                         ctx.rewind(3);
//                     }
//                     for advice in self.advices.iter().skip(chunk.len()) {
//                         ctx.empty((*advice).into())?;
//                         ctx.next();
//                         ctx.empty((*advice).into())?;
//                         ctx.next();
//                         ctx.empty((*advice).into())?;
//                         ctx.next();
//                         ctx.empty((*advice).into())?;
//                         ctx.rewind(3);
//                     }

//                     ctx.advance(4);
//                 }

//                 Ok(ctx.offset())
//             },
//         )?;

//         #[cfg(feature = "inspect")]
//         {
//             println!("* rows: {_offset}");
//             println!();
//         }

//         Ok(())
//     }
// }
