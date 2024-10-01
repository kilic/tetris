use super::ac::AbstractCircuit;
use crate::{Error, Field, Term, Value, Var};
use std::collections::BTreeMap;

#[derive(Clone, Default, Debug)]
pub(crate) struct MemInspect {
    pub(crate) width: usize,
    pub(crate) write: usize,
    pub(crate) read: usize,
}

impl MemInspect {
    pub(crate) fn diff(&self, other: &MemInspect) -> MemInspect {
        MemInspect {
            width: self.width,
            write: self.write.checked_sub(other.write).unwrap(),
            read: self.read.checked_sub(other.read).unwrap(),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub enum MemIRConfig {
    // size of write once memory if applicable
    Active {
        width: usize,
    },
    #[default]
    NA,
}

impl From<usize> for MemIRConfig {
    fn from(width: usize) -> Self {
        if width == 0 {
            Self::NA
        } else {
            Self::Active { width }
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct MemWriteOnceIR<F: Field> {
    /// Entries written to the table
    pub entries: Vec<Entry<F>>,
    /// Queires read from the table
    pub queries: Vec<Query<F>>,
    /// Prover-time memory
    pub table: BTreeMap<(F, F), Vec<F>>,
    /// Size of memory vector
    pub cfg: MemIRConfig,
    // Seperate independent memory usage
    mem_segment_counter: u64,
}

#[derive(Clone, Debug)]
pub struct Entry<F: Field> {
    /// Seperate segments with a segment
    pub segment: F,
    /// Fine tuned address
    pub address: F,
    /// Entries to write
    pub values: Vec<Var<F>>,
}

impl<F: Field> Entry<F> {
    fn new(segment: F, address: F, values: &[Var<F>]) -> Self {
        Self {
            segment,
            address,
            values: values.to_vec(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Query<F: Field> {
    /// Seperate segments with a segment
    pub segment: F,
    /// Enforce pitch of the address
    pub address_offset: F,
    /// Fine tune address with a variable
    pub address_fine: Var<F>,
    /// Entries to recover
    pub values: Vec<Var<F>>,
}

impl<F: Field> Query<F> {
    pub fn new(segment: F, address_offset: F, address_fine: &Var<F>, values: &[Var<F>]) -> Self {
        Self {
            segment,
            address_offset,
            address_fine: *address_fine,
            values: values.to_vec(),
        }
    }
}

impl<F: Field> MemWriteOnceIR<F> {
    #[cfg(feature = "inspect")]
    pub(crate) fn inspect(&self) -> MemInspect {
        MemInspect {
            width: self.width().unwrap_or(0),
            write: self.entries.len(),
            read: self.queries.len(),
        }
    }

    pub(crate) fn new(cfg: MemIRConfig) -> Self {
        Self {
            entries: Vec::new(),
            queries: Vec::new(),
            table: BTreeMap::new(),
            cfg,
            mem_segment_counter: 1,
        }
    }

    pub(crate) fn width(&self) -> Option<usize> {
        match self.cfg {
            MemIRConfig::Active { width } => Some(width),
            MemIRConfig::NA => None,
        }
    }

    #[allow(dead_code)]
    pub(crate) fn next_segment(&mut self) -> F {
        let segment = self.mem_segment_counter;
        self.mem_segment_counter += 1;
        F::from_u64(segment)
    }
}

pub trait MemWriteOnceUnit<F: Field> {
    fn write(&mut self, segment: F, address: F, values: &[Var<F>]) -> Result<(), Error>;
    fn read(
        &mut self,
        segment: F,
        address_offset: F,
        address_fine: &Var<F>,
    ) -> Result<Vec<Var<F>>, Error>;
}

impl<F: Field> MemWriteOnceUnit<F> for AbstractCircuit<F> {
    fn write(&mut self, segment: F, address: F, values: &[Var<F>]) -> Result<(), Error> {
        let size = self.wo_mem_ir.width().ok_or(Error::Synthesis)?;
        (values.len() == size)
            .then_some(())
            .ok_or(Error::Synthesis)?;
        let entry = Entry::new(segment, address, values);
        self.wo_mem_ir.entries.push(entry);
        let values = values.iter().map(|value| value.value()).collect::<Vec<_>>();
        let values: Value<Vec<F>> = Value::from_iter(values);
        let key = (segment, address);
        values.maybe(|values| {
            let prev = self.wo_mem_ir.table.insert(key, values.clone());
            self.sanity_some(|| prev.map_or(Some(()), |prev| (prev == *values).then_some(())))
        })?;
        Ok(())
    }

    fn read(
        &mut self,
        segment: F,
        address_offset: F,
        address_fine: &Var<F>,
    ) -> Result<Vec<Var<F>>, Error> {
        let width = self.wo_mem_ir.width().expect("inactive");
        let values = address_fine.value().maybe(|address_fine| {
            let address = *address_fine + address_offset;
            let key = (segment, address);
            self.wo_mem_ir.table.get(&key).cloned()
        })?;
        let values = values.transpose_vec(width);
        let values = values
            .into_iter()
            .map(|value| self.var(&value))
            .collect::<Vec<_>>();
        let query = Query::new(segment, address_offset, address_fine, &values);
        self.wo_mem_ir.queries.push(query);
        Ok(values)
    }
}

#[derive(Debug, Clone, Default)]
pub struct MemReadOnlyIR<F: Field> {
    /// Queires read from the table
    pub(crate) queries: Vec<Query<F>>,
    /// Actual memory
    pub(crate) table: BTreeMap<(F, F), Vec<F>>,
    /// Size of memory vector
    pub(crate) cfg: MemIRConfig,
}

impl<F: Field> MemReadOnlyIR<F> {
    #[cfg(feature = "inspect")]
    pub(crate) fn inspect(&self) -> MemInspect {
        MemInspect {
            width: self.width().unwrap_or(0),
            write: self.table.len(),
            read: self.queries.len(),
        }
    }

    pub(crate) fn new(cfg: MemIRConfig) -> Self {
        Self {
            queries: Vec::new(),
            table: BTreeMap::new(),
            cfg,
        }
    }

    pub(crate) fn width(&self) -> Option<usize> {
        match self.cfg {
            MemIRConfig::Active { width } => Some(width),
            MemIRConfig::NA => None,
        }
    }
}

pub trait MemReadOnlyUnit<F: Field> {
    fn write(&mut self, segment: F, address: F, values: &[F]) -> Result<(), Error>;
    fn read(
        &mut self,
        segment: F,
        address_offset: F,
        address_fine: &Var<F>,
    ) -> Result<Vec<Var<F>>, Error>;
}

impl<F: Field> MemReadOnlyUnit<F> for AbstractCircuit<F> {
    fn write(&mut self, segment: F, address: F, values: &[F]) -> Result<(), Error> {
        let size = self.ro_mem_ir.width().ok_or(Error::Synthesis)?;
        (values.len() == size)
            .then_some(())
            .ok_or(Error::Synthesis)?;
        let key = (segment, address);
        let prev = self.ro_mem_ir.table.insert(key, values.to_vec());
        self.sanity_some(|| prev.map_or(Some(()), |prev| (prev == *values).then_some(())))
            .ok_or(Error::Prover)
    }

    fn read(
        &mut self,
        segment: F,
        address_offset: F,
        address_fine: &Var<F>,
    ) -> Result<Vec<Var<F>>, Error> {
        let width = self.ro_mem_ir.width().ok_or(Error::Synthesis)?;
        let values = address_fine.value().maybe(|address_fine| {
            let address = *address_fine + address_offset;
            let key = (segment, address);
            self.ro_mem_ir.table.get(&key).cloned()
        })?;
        let values = values.transpose_vec(width);
        let values = values
            .iter()
            .map(|value| self.var(value))
            .collect::<Vec<_>>();
        let query = Query::new(segment, address_offset, address_fine, &values);
        self.ro_mem_ir.queries.push(query);
        Ok(values)
    }
}
