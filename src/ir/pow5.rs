use crate::{qc, Term, Field, Value, Var};

use super::{
    ac::AbstractCircuit,
    combination::{quad::Qc, CombinationGadget},
};

#[derive(Debug, Clone, Default)]
pub struct Pow5<F: Field> {
    pub w1: Var<F>,
    pub w2: Value<F>,
    pub w3: Value<F>,
    pub w5: Var<F>,
}

impl<F: Field> Pow5<F> {
    pub fn new(w1: Var<F>, w2: Value<F>, w3: Value<F>, w5: Var<F>) -> Self {
        Self { w1, w2, w3, w5 }
    }
}

#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub enum Pow5IRConfig {
    #[default]
    // apply with algebraic gate
    Combo,
    // apply with a^5 special gate
    Gated,
}

#[derive(Default, Clone)]
pub struct Pow5IR<F: Field> {
    pub(crate) cfg: Pow5IRConfig,
    pub(crate) gated: Vec<Pow5<F>>,
    #[cfg(feature = "inspect")]
    pub(crate) n: usize,
}

impl<F: Field> Pow5IR<F> {
    pub fn new(cfg: Pow5IRConfig) -> Self {
        Self {
            cfg,
            ..Default::default()
        }
    }
}

impl<F: Field> AbstractCircuit<F> {
    pub fn pow5(&mut self, w: &Var<F>) -> Var<F> {
        #[cfg(feature = "inspect")]
        {
            self.pow5_ir.n += 1;
        }
        match self.pow5_ir.cfg {
            Pow5IRConfig::Combo => {
                let w2 = self.eval(qc!() + w * w);
                let w3 = self.eval(qc!() + w2 * w);
                self.eval(qc!() + w3 * w2)
            }
            Pow5IRConfig::Gated => {
                let w1 = w.value();
                let w2 = w1 * w1;
                let w3 = w2 * w1;
                let w5 = w3 * w2;
                let w5 = self.var(&w5);
                self.pow5_ir.gated.push(Pow5::new(*w, w2, w3, w5));
                w5
            }
        }
    }
}
