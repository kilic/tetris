use num_bigint::BigUint;

use super::{
    bitwise::{BitwiseIR, BitwiseIRConfig},
    combination::{
        linear::{Lc, LcCoeff, LcVar},
        quad::{QcCoeff, QcVar},
        CombinationGadget,
    },
    inspect::Inspect,
    mem::{MemIRConfig, MemReadOnlyIR, MemWriteOnceIR},
    pow5::{Pow5IR, Pow5IRConfig},
    range::RangeIR,
    select::{SelectIR, SelectIRConfig},
};
use crate::{lc, Error, Field, Term, Value, Var};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct AbstractConfig {
    pub mem_wo: MemIRConfig,
    pub mem_ro: MemIRConfig,
    pub select: SelectIRConfig,
    pub pow5: Pow5IRConfig,
    pub xor: BitwiseIRConfig,
    pub and: BitwiseIRConfig,
    pub sanity: bool,
}

impl AbstractConfig {
    pub fn new(
        mem_wo: MemIRConfig,
        mem_ro: MemIRConfig,
        select: SelectIRConfig,
        pow5: Pow5IRConfig,
        xor: BitwiseIRConfig,
        and: BitwiseIRConfig,
        sanity: bool,
    ) -> Self {
        Self {
            mem_wo,
            mem_ro,
            select,
            pow5,
            sanity,
            xor,
            and,
        }
    }
}

impl Default for AbstractConfig {
    fn default() -> Self {
        Self {
            mem_wo: MemIRConfig::default(),
            mem_ro: MemIRConfig::default(),
            select: SelectIRConfig::default(),
            pow5: Pow5IRConfig::default(),
            xor: BitwiseIRConfig::default(),
            and: BitwiseIRConfig::default(),
            sanity: true,
        }
    }
}

/// Prover time custom sanity check
pub fn sanity_ok<SAT, T>(check: bool, sat: SAT) -> Result<(), Error>
where
    SAT: FnOnce() -> Result<T, Error>,
{
    if check {
        sat().map(|_| ())?;
    }
    Ok(())
}

/// Prover time custom sanity check
pub fn sanity_some<SAT, T>(check: bool, sat: SAT) -> Option<()>
where
    SAT: FnOnce() -> Option<T>,
{
    if check {
        sat().map(|_| ())?;
    }
    Some(())
}

#[derive(Clone)]
pub struct AbstractCircuit<F: Field> {
    /// Var ids of public inputs
    pub(crate) public: Vec<Var<F>>,
    /// To give uniques id to vars
    pub(crate) n_var: u64,
    /// Store registred constants
    pub(crate) constants: BTreeMap<F, Var<F>>,
    /// Copies between vars
    pub(crate) copy: Vec<(u64, u64)>,
    /// Linear zero sum combinations
    pub(crate) lc: BTreeMap<LcCoeff<F>, Vec<LcVar<F>>>,
    /// Quadratic zero sum combinations
    pub(crate) qc: BTreeMap<QcCoeff<F>, Vec<QcVar<F>>>,
    /// Ranged combinations
    pub(crate) range_ir: RangeIR<F>,
    /// Conditional selections
    pub(crate) select_ir: SelectIR<F>,
    /// Poseidon special pow5 ir
    pub(crate) pow5_ir: Pow5IR<F>,
    /// Xor lookup ir
    pub(crate) xor_ir: BitwiseIR<F>,
    /// And lookup ir
    pub(crate) and_ir: BitwiseIR<F>,
    /// Write once memory
    pub(crate) wo_mem_ir: MemWriteOnceIR<F>,
    /// Write once memory
    pub(crate) ro_mem_ir: MemReadOnlyIR<F>,
    /// Prover time constrain check
    pub(crate) sanity: bool,
    // Native modulus
    pub(crate) modulus: BigUint,
    // Custom counter for various debug & reporting purposes
    pub(crate) counter: BTreeMap<String, u64>,
    /// Info at checkpoint
    pub(crate) checkpoint: Inspect,
}

impl<F: Field> AbstractCircuit<F> {
    pub fn new(cfg: AbstractConfig) -> Self {
        Self {
            wo_mem_ir: MemWriteOnceIR::new(cfg.mem_wo),
            ro_mem_ir: MemReadOnlyIR::new(cfg.mem_ro),
            select_ir: SelectIR::new(cfg.select),
            pow5_ir: Pow5IR::new(cfg.pow5),
            xor_ir: BitwiseIR::new(cfg.xor),
            and_ir: BitwiseIR::new(cfg.and),
            sanity: cfg.sanity,
            modulus: F::modulus(),
            ..Default::default()
        }
    }
}

impl<F: Field> Default for AbstractCircuit<F> {
    fn default() -> Self {
        Self {
            public: Vec::new(),
            n_var: 0,
            constants: BTreeMap::new(),
            copy: Vec::new(),
            lc: BTreeMap::new(),
            qc: BTreeMap::new(),
            range_ir: RangeIR::default(),
            select_ir: SelectIR::default(),
            pow5_ir: Pow5IR::default(),
            xor_ir: BitwiseIR::default(),
            and_ir: BitwiseIR::default(),
            wo_mem_ir: MemWriteOnceIR::default(),
            ro_mem_ir: MemReadOnlyIR::default(),
            checkpoint: Inspect::default(),
            sanity: true,
            modulus: F::modulus(),
            counter: BTreeMap::new(),
        }
    }
}

impl<F: Field> AbstractCircuit<F> {
    pub fn get_log(&self, key: &str) -> u64 {
        *self.counter.get(key).unwrap_or(&0)
    }

    pub fn log_incr(&mut self, key: &str) {
        *self.counter.entry(key.to_string()).or_insert(0) += 1;
    }

    pub fn log_max(&mut self, key: &str, e1: u64) {
        self.counter
            .entry(key.to_string())
            .and_modify(|e0| *e0 = std::cmp::max(*e0, e1))
            .or_insert(e1);
    }

    pub fn log(&mut self, key: &str, e0: u64) {
        self.counter
            .entry(key.to_string())
            .and_modify(|e1| *e1 = e0)
            .or_insert(e0);
    }

    /// New **unassigned** public input
    pub fn public(&mut self, var: &Var<F>) {
        self.public.push(*var);
    }

    /// New **unassigned** variable
    pub fn var(&mut self, value: &Value<F>) -> Var<F> {
        self.n_var += 1;
        Var::new(self.n_var, value)
    }

    pub fn switch_sanity_check(&mut self, sanity: bool) {
        self.sanity = sanity;
    }

    /// Prover time custom sanity check
    pub fn sanity_ok<SAT, T>(&self, sat: SAT) -> Result<(), Error>
    where
        SAT: FnOnce() -> Result<T, Error>,
    {
        sanity_ok(self.sanity, sat)
    }

    /// Prover time custom sanity check
    pub fn sanity_some<SAT, T>(&self, sat: SAT) -> Option<()>
    where
        SAT: FnOnce() -> Option<T>,
    {
        sanity_some(self.sanity, sat)
    }

    /// **DOES NOT GUARANTEE ASSIGNMENT OF THE VARIABLE**
    /// Enfoce equaility between two vars
    pub fn equal(&mut self, w0: &Var<F>, w1: &Var<F>) -> Result<(), Error> {
        self.sanity_ok(|| w0.eq(w1).maybe(|e| e.then_some(())))?;

        match (w0.id, w1.id) {
            (Some(id0), Some(id1)) => {
                self.copy.push((id0, id1));
            }
            _ => panic!("cannot copy tmp variable"),
        };

        Ok(())
    }

    /// Assigns new constant to a variable. If exists already returns the assigned
    pub fn get_constant(&mut self, constant: F) -> Var<F> {
        match self.constants.get(&constant) {
            Some(constant) => *constant,
            _ => {
                let w = self.eval(lc!(constant));
                self.constants.insert(constant, w);
                w
            }
        }
    }
}
