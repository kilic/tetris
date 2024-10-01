use super::ac::AbstractCircuit;
use crate::{Field, Term, Var};

#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub enum BitwiseIRConfig {
    #[default]
    // not applicable
    NA,
    // apply with lookup
    Lookup {
        num_bits: usize,
    },
}

#[derive(Clone, Default)]
pub struct Bitwise<F: Field> {
    pub v0: Var<F>,
    pub v1: Var<F>,
    pub res: Var<F>,
}

impl<F: Field> Bitwise<F> {
    pub fn new(v0: Var<F>, v1: Var<F>, res: Var<F>) -> Self {
        Self { v0, v1, res }
    }
}

#[derive(Default, Clone)]
pub struct BitwiseIR<F: Field> {
    pub(crate) cfg: BitwiseIRConfig,
    pub(crate) lookups: Vec<Bitwise<F>>,
    #[cfg(feature = "inspect")]
    pub(crate) n: usize,
}

impl<F: Field> BitwiseIR<F> {
    pub fn new(cfg: BitwiseIRConfig) -> Self {
        Self {
            cfg,
            ..Default::default()
        }
    }
}

impl<F: Field> AbstractCircuit<F> {
    pub fn xor_word(&mut self, v0: &Var<F>, v1: &Var<F>) -> Var<F> {
        #[cfg(feature = "inspect")]
        {
            self.xor_ir.n += 1;
        }
        match self.xor_ir.cfg {
            BitwiseIRConfig::NA => {
                panic!()
            }
            BitwiseIRConfig::Lookup { num_bits: _ } => {
                let v0 = v0.value();
                let v1 = v1.value();
                let res = v0.zip(v1).map(|(v0, v1)| {
                    let e = v0.uint() ^ v1.uint();
                    F::from_uint(&e).unwrap()
                });
                let v0 = self.var(&v0);
                let v1 = self.var(&v1);
                let res = self.var(&res);
                self.xor_ir.lookups.push(Bitwise::new(v0, v1, res));
                res
            }
        }
    }
}

impl<F: Field> AbstractCircuit<F> {
    pub fn and_word(&mut self, v0: &Var<F>, v1: &Var<F>) -> Var<F> {
        #[cfg(feature = "inspect")]
        {
            self.and_ir.n += 1;
        }
        match self.and_ir.cfg {
            BitwiseIRConfig::NA => {
                panic!()
            }
            BitwiseIRConfig::Lookup { num_bits: _ } => {
                let v0 = v0.value();
                let v1 = v1.value();
                let res = v0.zip(v1).map(|(v0, v1)| {
                    let e = v0.uint() & v1.uint();
                    F::from_uint(&e).unwrap()
                });
                let v0 = self.var(&v0);
                let v1 = self.var(&v1);
                let res = self.var(&res);
                self.and_ir.lookups.push(Bitwise::new(v0, v1, res));
                res
            }
        }
    }
}
