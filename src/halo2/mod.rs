use crate::{Term, Var};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, Value},
    halo2curves::ff::PrimeField,
    plonk::{Advice, Any, Column, ErrorFront, Fixed, Selector},
};
use std::collections::BTreeMap;

pub mod acc;
pub mod bitwise;
pub mod config;
pub mod mem_static;
pub mod mem_write_once;
pub mod pi;
pub mod pow5;
pub mod range;
pub mod select;

#[cfg(test)]
pub mod test;

pub type AssignedValue<F> = AssignedCell<F, F>;
pub type CellMap<F> = BTreeMap<u64, AssignedValue<F>>;

#[derive(Debug)]
pub struct LayoutCtx<F: PrimeField, L: Layouter<F>> {
    pub layouter: L,
    pub cell_map: CellMap<F>,
    pub sanity: bool,
}

impl<F: PrimeField + Ord, L: Layouter<F>> LayoutCtx<F, L> {
    pub fn new(layouter: L) -> Self {
        LayoutCtx {
            layouter,
            cell_map: BTreeMap::new(),
            sanity: false,
        }
    }

    pub fn region<'a>(&mut self, region: Region<'a, F>) -> RegionCtx<'a, '_, F> {
        RegionCtx::new(region, &mut self.cell_map)
    }

    pub fn apply_indirect_copies(&mut self, copies: &[(u64, u64)]) -> Result<(), ErrorFront> {
        self.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut RegionCtx::new(region, &mut self.cell_map);
                for (id0, id1) in copies.iter() {
                    ctx.copy(*id0, *id1)?;
                }
                Ok(())
            },
        )
    }

    pub fn switch_sanity_check(&mut self, sanity: bool) {
        self.sanity = sanity;
    }
}

#[derive(Debug)]
pub struct RegionCtx<'a, 'b, F: PrimeField> {
    region: Region<'a, F>,
    offset: usize,
    cell_map: &'b mut CellMap<F>,
}

impl<'a, 'b, F: PrimeField + Ord> RegionCtx<'a, 'b, F> {
    pub fn new(region: Region<'a, F>, cell_map: &'b mut CellMap<F>) -> RegionCtx<'a, 'b, F> {
        RegionCtx {
            region,
            offset: 0,
            cell_map,
        }
    }

    pub fn copy(&mut self, id0: u64, id1: u64) -> Result<(), ErrorFront> {
        let cell0 = self
            .cell_map
            .get(&id0)
            .unwrap_or_else(|| panic!("must be assigned to apply copy constrain: {id0}"));
        let cell1 = self
            .cell_map
            .get(&id1)
            .unwrap_or_else(|| panic!("must be assigned to apply copy constrain: {id1}"));
        self.region.constrain_equal(cell0.cell(), cell1.cell())
    }

    pub fn offset(&self) -> usize {
        self.offset
    }

    pub fn fixed(&mut self, column: Column<Fixed>, value: F) -> Result<(), ErrorFront> {
        self.region
            .assign_fixed(|| "", column, self.offset(), || Value::known(value))?;
        Ok(())
    }

    pub fn advice_temp(&mut self, column: Column<Advice>, w: &Value<F>) -> Result<(), ErrorFront> {
        let _ = self
            .region
            .assign_advice(|| "temp", column, self.offset(), || *w)?;
        Ok(())
    }

    pub fn advice(&mut self, column: Column<Advice>, w: &Var<F>) -> Result<(), ErrorFront> {
        let cell = self
            .region
            .assign_advice(|| "", column, self.offset(), || w.value().halo2())?;
        if let Some(id) = w.id() {
            match self.cell_map.get(&id) {
                Some(root) => self.region.constrain_equal(root.cell(), cell.cell())?,
                None => {
                    self.cell_map.insert(id, cell);
                }
            }
        }
        Ok(())
    }

    pub fn empty(&mut self, column: Column<Any>) -> Result<(), ErrorFront> {
        match column.column_type() {
            Any::Advice => self.region.assign_advice(
                || "",
                column.try_into().unwrap(),
                self.offset,
                || Value::known(F::ZERO),
            ),
            Any::Fixed => self.region.assign_fixed(
                || "",
                column.try_into().unwrap(),
                self.offset,
                || Value::known(F::ZERO),
            ),
            _ => panic!("Cannot assign to instance column"),
        }?;
        Ok(())
    }

    pub fn enable(&mut self, selector: Selector) -> Result<(), ErrorFront> {
        selector.enable(&mut self.region, self.offset)
    }

    pub fn next(&mut self) {
        self.offset += 1;
    }

    pub fn advance(&mut self, n: usize) {
        self.offset += n;
    }

    pub fn rewind(&mut self, n: usize) {
        self.offset = self.offset.checked_sub(n).unwrap()
    }

    pub fn prev(&mut self) {
        self.offset = self.offset.checked_sub(1).unwrap();
    }
}
