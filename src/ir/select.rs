use super::{
    ac::AbstractCircuit,
    combination::{quad::Qc, CombinationGadget, CombinationIR},
};
use crate::{qc, Error, Field, Term, Var};

#[derive(Debug, Clone)]
pub struct Select<F: Field> {
    pub cond: Var<F>,
    pub w0: Var<F>,
    pub w1: Var<F>,
    pub selected: Var<F>,
}

impl<F: Field> Select<F> {
    pub fn new(cond: Var<F>, w0: Var<F>, w1: Var<F>, selected: Var<F>) -> Self {
        Select {
            cond,
            w0,
            w1,
            selected,
        }
    }
}

#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub enum SelectIRConfig {
    #[default]
    // apply with algebraic gate
    Combo,
    // apply with selection special gate
    Gated,
}

#[derive(Default, Clone)]
pub struct SelectIR<F: Field> {
    pub(crate) cfg: SelectIRConfig,
    pub(crate) gated: Vec<Select<F>>,
    #[cfg(feature = "inspect")]
    pub(crate) n: usize,
}

impl<F: Field> SelectIR<F> {
    pub fn new(cfg: SelectIRConfig) -> Self {
        Self {
            cfg,
            ..Default::default()
        }
    }
}

impl<F: Field> AbstractCircuit<F> {
    pub fn select(&mut self, cond: &Var<F>, w0: &Var<F>, w1: &Var<F>) -> Result<Var<F>, Error> {
        #[cfg(feature = "inspect")]
        {
            self.select_ir.n += 1;
        }
        self.sanity_ok(|| {
            cond.value()
                .maybe(|c| (c.square() - *c).is_zero().then_some(()))
        })?;

        let dif = self.sub(w1, w0);
        let qc = qc!() + dif * cond + w0;

        let selected = match self.select_ir.cfg {
            SelectIRConfig::Combo => self.eval(qc),
            SelectIRConfig::Gated => {
                let selected = qc.value();
                let selected = self.var(&selected);
                self.select_ir
                    .gated
                    .push(Select::new(*cond, *w0, *w1, selected));
                selected
            }
        };
        Ok(selected)
    }

    pub fn select_from_table(
        &mut self,
        cond: &[Var<F>],
        table: &[Var<F>],
    ) -> Result<Var<F>, Error> {
        assert!(!cond.is_empty());
        let n_cond = cond.len();
        let table_size = table.len();
        assert!(1 << (n_cond - 1) < table_size);

        let mut red = table.to_vec();
        for (i, cond) in cond.iter().enumerate() {
            let n = 1 << (n_cond - 1 - i);
            for j in 0..n {
                let k = 2 * j;
                match (red.get(k), red.get(k + 1)) {
                    (Some(w0), Some(w1)) => red[j] = self.select(cond, w0, w1)?,
                    (Some(w0), None) => red[j] = *w0,
                    _ => {}
                }
            }
        }
        Ok(*red.first().unwrap())
    }

    pub fn select_from_constant_table(
        &mut self,
        cond: &[Var<F>],
        table: &[F],
    ) -> Result<Var<F>, Error> {
        assert!(!cond.is_empty());
        let n_cond = cond.len();
        let table_size = table.len();
        assert!(1 << (n_cond - 1) < table_size);

        let mut red = vec![];
        for (i, cond) in cond.iter().enumerate() {
            let n = 1 << (n_cond - 1 - i);
            for j in 0..n {
                let k = 2 * j;
                if i == 0 {
                    match (table.get(k), table.get(k + 1)) {
                        (Some(t0), Some(t1)) => red.push(self.select_constant(cond, *t0, *t1)?),
                        (Some(t0), None) => red.push(self.get_constant(*t0)),
                        _ => {}
                    }
                } else {
                    match (red.get(k), red.get(k + 1)) {
                        (Some(w0), Some(w1)) => red[j] = self.select(cond, w0, w1)?,
                        (Some(w0), None) => red[j] = *w0,
                        _ => {}
                    }
                }
            }
        }
        Ok(*red.first().unwrap())
    }
}
