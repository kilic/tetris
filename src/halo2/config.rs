use super::{
    acc::QuadAccGate, bitwise::BitwiseGate, mem_static::MemReadOnlyGate,
    mem_write_once::MemWriteOnceGate, pi::PIGate, pow5::Pow5Gate, range::RangeGate,
    select::SelectGate, LayoutCtx,
};
use crate::{
    halo2::acc::LinearAccGate,
    ir::{
        ac::{AbstractCircuit, AbstractConfig},
        bitwise::BitwiseIRConfig,
        pow5::Pow5IRConfig,
        select::SelectIRConfig,
    },
};
use ark_std::{end_timer, start_timer};
use halo2_proofs::{
    circuit::Layouter,
    halo2curves::ff::PrimeField,
    plonk::{ConstraintSystem, ErrorFront, FirstPhase, SecondPhase},
};

#[derive(Clone, Copy)]
pub enum RangeGateConfig {
    /// Share exactly the same columns with quad gate
    Shared,
    /// Layouted right after quad gate. No intersection. Sized `n`.
    Separate { n: usize },
    // TODO: partial sharing might be considered in the future
}

#[derive(Clone, Copy)]
/// Gates with predefined width
pub struct StaticLayoutConfig {
    pub offset: usize,
}

#[derive(Clone, Copy)]
/// Lookup gates for `a op b = c` operations
pub struct TernaryLookupConfig {
    pub offset: usize,
    pub size_hint: usize,
}

/// Vector lookups gate config
#[derive(Clone, Copy)]
pub struct VectorLookupConfig {
    pub offset: usize,
    pub width: usize,
}

#[derive(Clone, Copy, Default)]
/// Offset is starting column index of the gate. For example if offset is 3
/// and gate is 4 columns wide, then gate column indexes are [3, 4, 5, 6]
pub struct GateConfig {
    /// Number of columns of quad gate. This is the main gate and offset is always zero.
    pub n_quad: usize,
    /// Range gate layout strategy
    pub range: Option<RangeGateConfig>,
    /// Read only memory config as `(number of columns, offset)`
    pub mem_ro: Option<VectorLookupConfig>,
    /// Write once memory config as `(number of columns, offset)`
    pub mem_wo: Option<VectorLookupConfig>,
    /// Select gate is 4 columns wide, configure the offset
    pub select: Option<StaticLayoutConfig>,
    /// Pow5 gate is 4 columns wide, configure the offset
    pub pow5: Option<StaticLayoutConfig>,
    /// Xor gate is 3 columns wide, configure (num_bits, offset)
    /// Table will be sized num_bits^2
    pub xor: Option<TernaryLookupConfig>,
    /// And gate is 3 columns wide, configure (num_bits, offset)
    /// Table will be sized num_bits^2
    pub and: Option<TernaryLookupConfig>,
    /// Check sanity when layouting. For instance: accumulator values
    pub sanity: bool,
}

impl GateConfig {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        n_quad: usize,
        range: Option<RangeGateConfig>,
        mem_ro: Option<VectorLookupConfig>,
        mem_wo: Option<VectorLookupConfig>,
        select: Option<StaticLayoutConfig>,
        pow5: Option<StaticLayoutConfig>,
        xor: Option<TernaryLookupConfig>,
        and: Option<TernaryLookupConfig>,
        sanity: bool,
    ) -> Self {
        Self {
            n_quad,
            range,
            mem_ro,
            mem_wo,
            select,
            pow5,
            sanity,
            xor,
            and,
        }
    }

    pub fn abstract_cfg(&self) -> AbstractConfig {
        AbstractConfig::new(
            self.mem_wo
                .map(|VectorLookupConfig { offset: _, width }| width.into())
                .unwrap_or_default(),
            self.mem_ro
                .map(|VectorLookupConfig { offset: _, width }| width.into())
                .unwrap_or_default(),
            self.select
                .map(|_| SelectIRConfig::Gated)
                .unwrap_or_default(),
            self.pow5.map(|_| Pow5IRConfig::Gated).unwrap_or_default(),
            self.xor
                .map(
                    |TernaryLookupConfig {
                         offset: _,
                         size_hint,
                     }| BitwiseIRConfig::Lookup {
                        num_bits: size_hint,
                    },
                )
                .unwrap_or_default(),
            self.and
                .map(
                    |TernaryLookupConfig {
                         offset: _,
                         size_hint,
                     }| BitwiseIRConfig::Lookup {
                        num_bits: size_hint,
                    },
                )
                .unwrap_or_default(),
            self.sanity,
        )
    }

    fn number_of_colums(&self) -> usize {
        let mut n = self.n_quad;

        if let Some(RangeGateConfig::Separate { n: n_range }) = self.range {
            n += n_range;
        };

        if let Some(VectorLookupConfig { offset, width }) = self.mem_ro {
            n = std::cmp::max(n, offset + width + 1);
        }

        if let Some(VectorLookupConfig { offset, width }) = self.mem_wo {
            n = std::cmp::max(n, offset + width + 1);
        }

        if let Some(StaticLayoutConfig { offset }) = self.select {
            n = std::cmp::max(n, offset + 4);
        }

        if let Some(StaticLayoutConfig { offset }) = self.pow5 {
            n = std::cmp::max(n, offset + 4);
        }

        if let Some(TernaryLookupConfig {
            offset,
            size_hint: _,
        }) = self.xor
        {
            n = std::cmp::max(n, offset + 3);
        }

        if let Some(TernaryLookupConfig {
            offset,
            size_hint: _,
        }) = self.and
        {
            n = std::cmp::max(n, offset + 3);
        }

        n
    }
}

#[derive(Clone)]
pub struct Gates {
    pi: PIGate,
    quad: QuadAccGate,
    range: Option<RangeGate>,
    mem_ro: Option<MemReadOnlyGate>,
    mem_wo: Option<MemWriteOnceGate>,
    select: Option<SelectGate>,
    xor: Option<BitwiseGate>,
    and: Option<BitwiseGate>,
    pow5: Option<Pow5Gate>,
}

impl Gates {
    pub fn configure<F: PrimeField + Ord>(
        meta: &mut ConstraintSystem<F>,
        cfg: &GateConfig,
    ) -> Self {
        let n_columns = cfg.number_of_colums();

        let advices = std::iter::repeat(())
            .take(n_columns)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>();

        let alpha = meta.challenge_usable_after(FirstPhase);
        let acc = meta.advice_column_in(SecondPhase);
        let constant = meta.fixed_column();
        let coeff = meta.fixed_column();

        let quad =
            QuadAccGate::configure(meta, &coeff, &advices[..cfg.n_quad], &constant, alpha, &acc);
        let pi = PIGate::configure(meta, advices[0]);

        let range = cfg.range.as_ref().map(|range| match range {
            RangeGateConfig::Shared => {
                #[cfg(feature = "inspect")]
                {
                    println!("---------");
                    println!("Gates::configure");
                    println!("# advice: {}", n_columns + 1);
                    println!()
                }
                RangeGate::configure(meta, quad.linear_gate())
            }

            RangeGateConfig::Separate { n: n_range } => {
                #[cfg(feature = "inspect")]
                {
                    println!("---------");
                    println!("Gates::configure");
                    println!("# advice: {}", n_columns + 2);
                    println!()
                }

                let acc = meta.advice_column_in(SecondPhase);
                let constant = meta.fixed_column();
                let coeff = meta.fixed_column();
                let acc_gate = LinearAccGate::configure(
                    meta,
                    &coeff,
                    &advices[cfg.n_quad..cfg.n_quad + n_range],
                    &constant,
                    alpha,
                    &acc,
                );
                RangeGate::configure(meta, acc_gate)
            }
        });

        let mem_ro = cfg.mem_ro.map(|VectorLookupConfig { offset, width }| {
            let query_fine = advices[offset];
            let query_vector = &advices[offset + 1..offset + 1 + width];
            MemReadOnlyGate::configure(meta, query_fine, query_vector)
        });

        let mem_wo = cfg.mem_wo.map(|VectorLookupConfig { offset, width }| {
            let query_fine = advices[offset];
            let query_vector = &advices[offset + 1..offset + 1 + width];
            MemWriteOnceGate::configure(meta, query_fine, query_vector)
        });

        let select = cfg.select.map(|StaticLayoutConfig { offset }| {
            let advices = advices[offset..offset + 4].try_into().unwrap();
            SelectGate::configure(meta, &advices)
        });

        let pow5 = cfg.pow5.map(|StaticLayoutConfig { offset }| {
            let advices = advices[offset..offset + 4].try_into().unwrap();
            Pow5Gate::configure(meta, &advices)
        });

        let xor = cfg.xor.map(|TernaryLookupConfig { offset, size_hint }| {
            BitwiseGate::configure(
                meta,
                advices[offset..offset + 3].try_into().unwrap(),
                size_hint,
            )
        });

        let and = cfg.and.map(|TernaryLookupConfig { offset, size_hint }| {
            BitwiseGate::configure(
                meta,
                advices[offset..offset + 3].try_into().unwrap(),
                size_hint,
            )
        });

        Self {
            pi,
            quad,
            range,
            mem_ro,
            mem_wo,
            select,
            pow5,
            xor,
            and,
        }
    }

    pub fn layout<F: PrimeField + Ord, L: Layouter<F>>(
        &self,
        ly: &mut LayoutCtx<F, L>,
        ac: &AbstractCircuit<F>,
    ) -> Result<(), ErrorFront> {
        let t_layout = start_timer!(|| "layout");
        self.pi.layout(ly, &ac.public)?;
        self.quad.layout(ly, &ac.qc)?;
        self.quad.linear_gate().layout(ly, &ac.lc)?;

        if let Some(range) = &self.range {
            let bit_sizes = range.layout(ly, &ac.range_ir)?;
            range.layout_tables(ly, &bit_sizes)?;
        } else {
            assert!(ac.range_ir.singles.is_empty());
            assert!(ac.range_ir.combinations.is_empty());
            assert!(ac.range_ir.sizes.is_empty());
        }

        if let Some(gate) = &self.mem_ro {
            gate.layout(ly, &ac.ro_mem_ir)?;
        } else {
            assert!(ac.ro_mem_ir.table.is_empty());
            assert!(ac.ro_mem_ir.queries.is_empty());
            assert!(ac.ro_mem_ir.width().is_none());
        }

        if let Some(gate) = &self.mem_wo {
            gate.layout(ly, &ac.wo_mem_ir)?;
        } else {
            assert!(ac.wo_mem_ir.table.is_empty());
            assert!(ac.wo_mem_ir.entries.is_empty());
            assert!(ac.wo_mem_ir.queries.is_empty());
            assert!(ac.wo_mem_ir.width().is_none());
        }

        if let Some(gate) = &self.select {
            gate.layout(ly, &ac.select_ir.gated)?;
        } else {
            assert!(ac.select_ir.gated.is_empty());
            assert_eq!(ac.select_ir.cfg, SelectIRConfig::Combo);
        }

        if let Some(gate) = &self.pow5 {
            gate.layout(ly, &ac.pow5_ir.gated)?;
        } else {
            assert!(ac.pow5_ir.gated.is_empty());
            assert_eq!(ac.pow5_ir.cfg, Pow5IRConfig::Combo);
        }

        if let Some(gate) = &self.xor {
            gate.layout_xor_table(ly)?;
            gate.layout(ly, &ac.xor_ir.lookups)?;
        } else {
            assert!(ac.xor_ir.lookups.is_empty());
            assert_eq!(ac.xor_ir.cfg, BitwiseIRConfig::NA);
        }

        if let Some(gate) = &self.and {
            gate.layout_and_table(ly)?;
            gate.layout(ly, &ac.and_ir.lookups)?;
        } else {
            assert!(ac.and_ir.lookups.is_empty());
            assert_eq!(ac.and_ir.cfg, BitwiseIRConfig::NA);
        }

        ly.apply_indirect_copies(&ac.copy)?;
        end_timer!(t_layout);

        Ok(())
    }
}
