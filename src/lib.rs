pub mod gadget;
pub mod ir;
pub mod utils;
pub mod witness;

#[cfg(feature = "halo2")]
pub mod halo2;

pub use witness::field::Field;
pub use witness::value::Value;
pub use witness::Term;
pub use witness::{QuadScaled, QuadVar, Scaled, Var};

#[derive(Debug, Clone)]
pub enum Error {
    Invalid,
    Prover,
    Synthesis,
    Assignment,
    Debug(String),
}
