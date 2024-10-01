use std::collections::BTreeMap;

use crate::Field;

use super::{ac::AbstractCircuit, mem::MemInspect};

#[derive(Clone, Default)]
pub struct Inspect {
    n_var: u64,
    pi: usize,
    lc_map: BTreeMap<usize, usize>,
    qc_map: BTreeMap<(usize, usize), usize>,
    rc_map: BTreeMap<usize, usize>,
    // note that contribution of select also appears in lc and qc in ::Combo mode
    select: usize,
    // note that contribution of pow5 also appears in lc and qc in ::Combo mode
    pow5: usize,
    xor: usize,
    and: usize,
    mem_wo: MemInspect,
    mem_ro: MemInspect,
}

fn map_dif<T: Ord + Copy>(m1: &BTreeMap<T, usize>, m0: &BTreeMap<T, usize>) -> BTreeMap<T, usize> {
    let mut dif_map = BTreeMap::new();
    m1.iter().for_each(|(key, c1)| {
        let c0 = m0.get(key).unwrap_or(&0);
        let dif = c1.checked_sub(*c0).unwrap();
        (dif != 0).then(|| dif_map.insert(*key, dif));
    });
    dif_map
}

impl Inspect {
    fn print(&self, verbose: bool) -> usize {
        if verbose {
            println!("PI: {}", self.pi);
        }
        let mut n_eff_var = 0;
        n_eff_var += {
            if verbose {
                println!("LC: {}", self.lc_map.len());
            }
            let mut n_var = 0;
            self.lc_map.iter().for_each(|(n_terms, count)| {
                n_var += count * n_terms;
                if verbose {
                    println!(" * l: {n_terms} n: {count}")
                }
            });
            if verbose {
                println!(" * n_var: {}", n_var);
            }
            n_var
        };
        n_eff_var += {
            if verbose {
                println!("QC: {}", self.qc_map.len());
            }
            let mut n_var = 0;
            self.qc_map.iter().for_each(|((n_lin, n_quad), count)| {
                n_var += count * (n_lin + n_quad * 2);
                if verbose {
                    println!(" * l: {} q: {} n: {}", n_lin, n_quad, count)
                }
            });
            if verbose {
                println!(" * n_var: {}", n_var);
            }
            n_var
        };
        n_eff_var += {
            if verbose {
                println!("RC: {}", self.rc_map.len());
            }
            let mut n_var = 0;
            for (n_limbs, count) in self.rc_map.iter() {
                n_var += count * n_limbs;
                if verbose {
                    println!(" * l: {} n: {}", n_limbs, count);
                }
            }
            if verbose {
                println!(" * n_var: {}", n_var);
            }
            n_var
        };
        n_eff_var += self.select * 4;
        if verbose {
            println!("SEL: {}", self.select);
        }

        n_eff_var += self.mem_wo.write * self.mem_wo.width;
        n_eff_var += self.mem_wo.read * self.mem_wo.width;
        if verbose {
            println!("MWO: {:?}", self.mem_wo);
        }

        n_eff_var += self.mem_ro.read * self.mem_ro.width;
        if verbose {
            println!("MRO: {:?}", self.mem_ro);
        }

        n_eff_var += self.pow5 * 4;
        if verbose {
            println!("PW5: {}", self.pow5);
        }

        n_eff_var += self.xor * 3;
        if verbose {
            println!("XOR: {}", self.xor);
        }

        n_eff_var += self.and * 3;
        if verbose {
            println!("AND: {}", self.and);
        }

        n_eff_var
    }

    fn diff(&self, other: &Inspect) -> Inspect {
        Inspect {
            n_var: self.n_var - other.n_var,
            pi: self.pi - other.pi,
            lc_map: map_dif(&self.lc_map, &other.lc_map),
            qc_map: map_dif(&self.qc_map, &other.qc_map),
            rc_map: map_dif(&self.rc_map, &other.rc_map),
            select: self.select.checked_sub(other.select).unwrap(),
            pow5: self.pow5.checked_sub(other.pow5).unwrap(),
            xor: self.xor.checked_sub(other.xor).unwrap(),
            and: self.and.checked_sub(other.and).unwrap(),
            mem_wo: self.mem_wo.diff(&other.mem_wo),
            mem_ro: self.mem_wo.diff(&other.mem_ro),
        }
    }
}

#[cfg(feature = "inspect")]
impl<F: Field> AbstractCircuit<F> {
    pub(crate) fn inspect(&self) -> Inspect {
        Inspect {
            n_var: self.n_var,
            pi: self.public.len(),
            lc_map: self.flat_lc(),
            qc_map: self.flat_qc(),
            rc_map: self.flat_rc(),
            // note that when in ::Combo mode contribution also appears in lc and qc
            select: self.select_ir.n,
            // note that when in ::Combo mode contribution also appears in lc and qc
            pow5: self.pow5_ir.n,
            xor: self.xor_ir.n,
            and: self.and_ir.n,
            mem_wo: self.wo_mem_ir.inspect(),
            mem_ro: self.ro_mem_ir.inspect(),
        }
    }

    pub fn print_info(&self, _verbose: bool) {
        println!("AC_INSPECT:");
        println!("n_var: {}", self.n_var);
        // if verbose {
        //     println!("linear combinations verbose");
        //     self.lc.iter().for_each(|(key, witneses)| {
        //         println!("* #l: {} #n: {}", key.coeffs.len(), witneses.len())
        //     });
        // }
        // if verbose {
        //     println!("quad combinations verbose");
        //     self.qc.iter().for_each(|(key, witneses)| {
        //         println!(
        //             "* #l: {} q: {}, #n: {}",
        //             key.lin.len(),
        //             key.quad.len(),
        //             witneses.len()
        //         )
        //     });
        // }
        let n_eff_var = self.inspect().print(_verbose);
        println!("n_eff_var: {}", n_eff_var);
        println!("copy ratio: {}", self.n_var as f32 / n_eff_var as f32);
        println!();
    }

    pub fn checkpoint(&mut self) {
        self.checkpoint = self.inspect();
    }

    pub fn diff(&mut self, desc: &str, _verbose: bool) {
        println!("DIFF: {}, {} {}", desc, self.checkpoint.n_var, self.n_var);
        let current = self.inspect();
        let diff = current.diff(&self.checkpoint);
        let n_eff_var = diff.print(_verbose);
        println!("n_eff_var: {}", n_eff_var);
        self.checkpoint();
        println!();
    }

    fn flat_lc(&self) -> BTreeMap<usize, usize> {
        let mut flat: BTreeMap<usize, usize> = BTreeMap::new();

        for (coeffs, combos) in self.lc.iter() {
            let n = combos.len();
            flat.entry(coeffs.coeffs.len())
                .and_modify(|count| *count += n)
                .or_insert_with(|| n);
        }

        flat
    }

    fn flat_qc(&self) -> BTreeMap<(usize, usize), usize> {
        let mut flat: BTreeMap<(usize, usize), usize> = BTreeMap::new();
        for (coeffs, combos) in self.qc.iter() {
            let n = combos.len();
            flat.entry((coeffs.lin.len(), coeffs.quad.len()))
                .and_modify(|count| *count += n)
                .or_insert_with(|| n);
        }

        flat
    }

    fn flat_rc(&self) -> BTreeMap<usize, usize> {
        let mut flat: BTreeMap<usize, usize> = BTreeMap::new();
        for (key, combos) in self.range_ir.combinations.iter() {
            let n = combos.len();
            flat.entry(key.sizes.len())
                .and_modify(|count| *count += n)
                .or_insert_with(|| n);
        }
        flat
    }
}
