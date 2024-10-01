use crate::{gadget::big_field::VarBig, ir::ac::AbstractCircuit, Field};
use blake2::Blake2b512;
use digest::Digest;
use itertools::Itertools;

use super::{Curve, EccGadget, Point};

#[cfg(test)]
pub(crate) fn multiexp<C: crate::gadget::ecc::Curve>(point: &[C], scalar: &[C::Scalar]) -> C {
    assert!(!point.is_empty());
    assert_eq!(point.len(), scalar.len());
    point
        .iter()
        .zip_eq(scalar.iter())
        .fold(C::identity(), |acc, (point, scalar)| {
            acc + (*point * *scalar)
        })
}

pub trait EccMulGadget<C: Curve, N: Field>: EccGadget<C, N> {
    fn hash_points_to_field(person: &str, points: &[C]) -> N {
        let mut h = Blake2b512::new_with_prefix(person.as_bytes());
        points.iter().for_each(|point| h.update(point.to_bytes()));
        N::from_bytes_red(h.finalize().as_ref())
    }

    fn mul_fix_vertical_extended(
        &self,
        ac: &mut AbstractCircuit<N>,
        window: usize,
        point: &C,
        scalar: &Self::Scalar,
    ) -> Point<VarBig<N>> {
        let person = "ecc-gadget-mul-fix-vertical-extended";
        let aux = C::hash_to_curve(person, &[]);
        // Extend tables where `window = 2` and `A` is aux and `P` is the point
        // `t0 = [   A,    A +  1*P,   A + 2*P,   A +  3*P]`
        // `t1 = [ 2*A,  2*A +  2*P, 2*A + 8*P, 2*A + 12*P]`
        // ...and so on up to `t_(n_rounds-1)`
        let (tables, correction) = point.extended_table(&aux, window);
        // And correction point `correction = sum(A, 2*A, 3*A, n_rounds*A)`
        let correction = self.get_constant(ac, &correction.neg());

        // Make table elements into non native constant form
        let tables = tables
            .iter()
            .map(|t| t.iter().map(|p| self.constant_point(p)).collect_vec())
            .collect_vec();

        // Scalar to bits
        let scalar = self.decompose_scalar(ac, 1, scalar).unwrap();

        // Select points from the round-tables and plus the correction
        let add_chain = scalar
            .chunks(window)
            .zip_eq(tables.iter())
            .map(|(s, t)| self.select_from_constant_table(ac, s, t).unwrap())
            .chain(std::iter::once(correction))
            .collect_vec();
        self.add_chain(ac, &add_chain)
    }

    fn msm_fix_vertical_extended(
        &self,
        ac: &mut AbstractCircuit<N>,
        window: usize,
        points: &[C],
        scalars: &[Self::Scalar],
    ) -> Point<VarBig<N>> {
        assert!(!points.is_empty());
        let add_chain = points
            .iter()
            .zip_eq(scalars)
            .map(|(point, scalar)| self.mul_fix_vertical_extended(ac, window, point, scalar))
            .collect_vec();
        self.add_chain(ac, &add_chain)
    }

    fn mul_fix_vertical_extended_mem(
        &self,
        ac: &mut AbstractCircuit<N>,
        window: usize,
        point: &C,
        scalar: &Self::Scalar,
    ) -> Point<VarBig<N>> {
        // personalize theoperation
        let person = "ecc-gadget-mul-fix-vertical-extended";

        // Determine memory segment for this point
        let mem_segment = Self::hash_points_to_field(person, &[*point]);

        // Constant aux introduces incompleteness factor may result in DOS vector depending on the use case
        let aux = C::hash_to_curve(person, &[]);

        // Extend tables where `window = 2` and `A` is aux and `P` is the point
        // `t0 = [   A,    A +  1*P,   A + 2*P,   A +  3*P]`
        // `t1 = [ 2*A,  2*A +  2*P, 2*A + 8*P, 2*A + 12*P]`
        // ...and so on up to `t_(n_rounds-1)`
        let (tables, correction) = point.extended_table(&aux, window);
        // And correction point `correction = sum(A, 2*A, 3*A, n_rounds*A)`
        let correction = self.get_constant(ac, &correction.neg());

        // Write points to the static memory
        let table_size = 1 << window;
        let n_rounds = num_integer::div_ceil(N::num_bits(), window);
        let points_offset = 2 * table_size * n_rounds;
        tables.iter().enumerate().for_each(|(round, round_table)| {
            let round_offset = 2 * table_size * round + points_offset;
            round_table
                .iter()
                .enumerate()
                .for_each(|(point_idx, point)| {
                    let address = N::from_u64((round_offset + point_idx) as u64);
                    self.write_constant(ac, mem_segment, address, table_size, point)
                        .unwrap();
                });
        });

        // Scalar to bits
        let scalar = self.decompose_scalar(ac, window, scalar).unwrap();

        // Select points from the round-tables and plus the correction
        let add_chain = scalar
            .iter()
            .enumerate()
            .map(|(round, selector)| {
                let round_offset = 2 * table_size * round + points_offset;
                let address_offset = N::from_u64(round_offset as u64);
                self.read_constant(ac, mem_segment, address_offset, selector, table_size)
                    .unwrap()
            })
            .chain(std::iter::once(correction))
            .collect_vec();
        self.add_chain(ac, &add_chain)
    }

    fn msm_fix_vertical_extended_mem(
        &self,
        ac: &mut AbstractCircuit<N>,
        window: usize,
        points: &[C],
        scalars: &[Self::Scalar],
    ) -> Point<VarBig<N>> {
        assert!(!points.is_empty());
        let add_chain = points
            .iter()
            .zip_eq(scalars)
            .map(|(point, scalar)| self.mul_fix_vertical_extended_mem(ac, window, point, scalar))
            .collect_vec();
        self.add_chain(ac, &add_chain)
    }

    fn msm_fix_vertical_mem(
        &self,
        ac: &mut AbstractCircuit<N>,
        window: usize,
        points: &[C],
        scalars: &[Self::Scalar],
    ) -> Point<VarBig<N>> {
        let n_points = points.len();
        assert!(n_points > 0);

        let n_rounds = num_integer::div_ceil(C::Scalar::num_bits(), window);
        let table_size = 1 << window;

        let person = "ecc-gadget-msm-fix-vertical";
        // Generate deterministic aux points for each point
        let aux = (0..n_points)
            .map(|point_idx| C::hash_to_curve(format!("{person}-{point_idx}").as_str(), &[]))
            .collect_vec();

        // Emulate the multiplicaion and find the effective aux contribution
        let aux_sum = C::sum(&aux);
        let correction = (0..n_rounds).fold(C::identity(), |acc, _| {
            (0..window).fold(acc, |acc, _| acc.double()) + aux_sum
        });
        let correction = self.get_constant(ac, &correction);

        let mem_segment = points
            .iter()
            .zip_eq(aux)
            .enumerate()
            .map(|(point_idx, (point, aux))| {
                // Determine the memory segment for this point
                let mem_segment =
                    Self::hash_points_to_field(format!("{person}-{point_idx}").as_str(), &[*point]);

                // Make the incremental table
                // `t_i = [A_i, A_i + 1*P_i, A_i + 2*P_i, A_i + ... ]`
                let table = point.incremental_table(1 << window, &aux);

                // Write to the table
                table.iter().enumerate().for_each(|(i, point)| {
                    self.write_constant(ac, mem_segment, N::from_u64(i as u64), table_size, point)
                        .unwrap();
                });

                // return the memory segment to read from
                mem_segment
            })
            .collect_vec();

        // Decompose scalars into table indexes
        let scalars = scalars
            .iter()
            .map(|scalar| {
                let mut scalar = self.decompose_scalar(ac, window, scalar).unwrap();
                scalar.reverse();
                scalar
            })
            .collect_vec();

        let mut acc = None;
        for round in 0..n_rounds {
            acc = (0..window).fold(acc, |acc, _| {
                acc.map(|acc| self.double_incomplete(ac, &acc))
            });

            let add_chain = scalars
                .iter()
                .zip_eq(mem_segment.iter())
                .map(|(scalar, mem_segment)| {
                    self.read_constant(ac, *mem_segment, N::zero(), &scalar[round], table_size)
                        .unwrap()
                })
                .chain(acc)
                .collect_vec();

            acc = Some(self.add_chain(ac, &add_chain));
        }

        self.sub_incomplete(ac, &acc.unwrap(), &correction)
    }

    fn msm_fix_horizontal_mem(
        &self,
        ac: &mut AbstractCircuit<N>,
        window: usize,
        points: &[C],
        scalars: &[Self::Scalar],
    ) -> Point<VarBig<N>> {
        assert!(!points.is_empty());
        let n_rounds = C::Scalar::num_bits();
        let person = "ecc-gadget-msm-fix-horizontal";

        // Generate deterministic aux points for each chunk of points
        let aux = points
            .chunks(window)
            .enumerate()
            .map(|(chunk_idx, _)| C::hash_to_curve(format!("{person}-{chunk_idx}").as_str(), &[]))
            .collect_vec();
        // Emulate the multiplicaion and find the effective aux contribution
        let aux_sum = C::sum(&aux);
        let correction = (0..n_rounds).fold(C::identity(), |acc, _| acc.double() + aux_sum);
        let correction = self.get_constant(ac, &correction);

        let table_size = 1 << window;
        let mem_segment = points
            .chunks(window)
            .zip_eq(aux)
            .enumerate()
            .map(|(chunk_idx, (chunk, round_aux))| {
                // Determine the memory segment for this chunk
                let mem_segment =
                    Self::hash_points_to_field(format!("{person}-{chunk_idx}").as_str(), chunk);

                // example table for window = 3
                // A
                // A + P_0
                // A + P_1
                // A + P_0 + P_1
                // A + P_2
                // A + P_0 + P_2
                // A + P_1 + P_2
                // A + P_0 + P_1 + P_2

                let mut table = vec![round_aux];
                self.write_constant(
                    ac,
                    mem_segment,
                    N::zero(),
                    table_size,
                    table.last().unwrap(),
                )
                .unwrap();

                chunk.iter().enumerate().for_each(|(i, point)| {
                    let b = 1 << i;
                    (0..b).for_each(|j| {
                        let address = N::from_u64((b + j) as u64);
                        table.push(table[j] + *point);
                        self.write_constant(
                            ac,
                            mem_segment,
                            address,
                            table_size,
                            table.last().unwrap(),
                        )
                        .unwrap();
                    });
                });
                mem_segment
            })
            .collect_vec();

        // Decompose scalars into bits
        let scalars = scalars
            .iter()
            .map(|scalar| {
                let mut scalar = self.decompose_scalar(ac, 1, scalar).unwrap();
                scalar.reverse();
                scalar
            })
            .collect_vec();

        let mut acc = None;
        for round in 0..(C::Scalar::num_bits()) {
            if let Some(acc) = acc.as_mut() {
                *acc = self.double_incomplete(ac, acc);
            }

            let add_chain = scalars
                .chunks(window)
                .zip_eq(mem_segment.iter())
                .map(|(scalars, mem_segment)| {
                    // Recover table index
                    let coeffs = scalars.iter().map(|e| e[round]).collect_vec();
                    let table_index = &ac.horner(&coeffs, N::from_u64(2));
                    // Get the point from the table
                    self.read_constant(ac, *mem_segment, N::zero(), table_index, table_size)
                        .unwrap()
                })
                .chain(acc)
                .collect_vec();

            acc = Some(self.add_chain(ac, &add_chain));
        }
        self.sub_incomplete(ac, &acc.unwrap(), &correction)
    }

    fn msm_var_vertical(
        &self,
        ac: &mut AbstractCircuit<N>,
        window: usize,
        points: &[Point<VarBig<N>>],
        scalars: &[Self::Scalar],
    ) -> Point<VarBig<N>> {
        let n_points = points.len();
        assert!(n_points > 0);

        let n_rounds = num_integer::div_ceil(C::Scalar::num_bits(), window);
        let table_size = 1 << window;

        // Generate deterministic aux points for each point
        let person = "ecc-gadget-msm-var-vertical";
        let aux = (0..n_points)
            .map(|point_idx| C::hash_to_curve(format!("{person}-{point_idx}").as_str(), &[]))
            .collect_vec();

        // Emulate the multiplicaion and find the effective aux contribution
        let aux_sum = C::sum(&aux);
        let correction = (0..n_rounds).fold(C::identity(), |acc, _| {
            (0..window).fold(acc, |acc, _| acc.double()) + aux_sum
        });
        let correction = self.get_constant(ac, &correction);

        let tables = points
            .iter()
            .zip_eq(aux)
            .map(|(point, aux)| {
                // Make the incremental table
                // `t_i = [A_i, A_i + 1*P_i, A_i + 2*P_i, A_i + ... ]`
                let aux = self.get_constant(ac, &aux);
                std::iter::successors(Some(aux), |prev| Some(self.add_incomplete(ac, prev, point)))
                    .take(table_size)
                    .collect_vec()
            })
            .collect_vec();

        // Decompose scalars into bit representation table indexes
        let scalars = scalars
            .iter()
            .map(|scalar| {
                let selector = self.decompose_scalar(ac, 1, scalar).unwrap();
                selector
                    .chunks(window)
                    .map(|chunk| chunk.to_vec())
                    .rev()
                    .collect_vec()
            })
            .collect_vec();

        let mut acc = None;
        for round in 0..n_rounds {
            acc = (0..window).fold(acc, |acc, _| {
                acc.map(|acc| self.double_incomplete(ac, &acc))
            });

            let add_chain = tables
                .iter()
                .zip_eq(scalars.iter())
                .map(|(table, scalar)| self.select_from_table(ac, &scalar[round], table).unwrap())
                .chain(acc)
                .collect_vec();

            acc = Some(self.add_chain(ac, &add_chain));
        }

        self.sub_incomplete(ac, &acc.unwrap(), &correction)
    }

    fn msm_var_vertical_with_mem(
        &self,
        ac: &mut AbstractCircuit<N>,
        window: usize,
        points: &[Point<VarBig<N>>],
        scalars: &[Self::Scalar],
    ) -> Point<VarBig<N>> {
        let n_points = points.len();
        assert!(n_points > 0);

        let n_rounds = num_integer::div_ceil(C::Scalar::num_bits(), window);
        let table_size = 1 << window;

        // Generate deterministic aux points for each point
        let person = "ecc-gadget-msm-var-vertical";
        let aux = (0..n_points)
            .map(|point_idx| C::hash_to_curve(format!("{person}-{point_idx}").as_str(), &[]))
            .collect_vec();

        // Emulate the multiplicaion and find the effective aux contribution
        let aux_sum = C::sum(&aux);
        let correction = (0..n_rounds).fold(C::identity(), |acc, _| {
            (0..window).fold(acc, |acc, _| acc.double()) + aux_sum
        });
        let correction = self.get_constant(ac, &correction);

        let mem_segment = points
            .iter()
            .zip_eq(aux)
            .map(|(point, aux)| {
                // Get unique memory segment for this point
                let mem_segment = ac.wo_mem_ir.next_segment();

                // Make the incremental table
                // `t_i = [A_i, A_i + 1*P_i, A_i + 2*P_i, A_i + ... ]`
                let aux = self.get_constant(ac, &aux);
                let table = std::iter::successors(Some(aux), |prev| {
                    Some(self.add_incomplete(ac, prev, point))
                })
                .take(table_size)
                .collect_vec();
                // And write to the memory
                table.iter().enumerate().for_each(|(point_idx, point)| {
                    self.write(
                        ac,
                        mem_segment,
                        N::from_u64(point_idx as u64),
                        table_size,
                        point,
                    )
                    .unwrap();
                });
                mem_segment
            })
            .collect_vec();

        // Decompose scalars into bits
        let scalars = scalars
            .iter()
            .map(|scalar| {
                let mut scalar = self.decompose_scalar(ac, window, scalar).unwrap();
                scalar.reverse();
                scalar
            })
            .collect_vec();

        let mut acc = None;
        for round in 0..n_rounds {
            acc = (0..window).fold(acc, |acc, _| {
                acc.map(|acc| self.double_incomplete(ac, &acc))
            });

            let add_chain = scalars
                .iter()
                .zip_eq(mem_segment.iter())
                .map(|(scalar, mem_segment)| {
                    self.read(ac, *mem_segment, N::zero(), &scalar[round], table_size)
                        .unwrap()
                })
                .chain(acc)
                .collect_vec();

            acc = Some(self.add_chain(ac, &add_chain));
        }

        self.sub_incomplete(ac, &acc.unwrap(), &correction)
    }

    fn msm_var_horizontal(
        &self,
        ac: &mut AbstractCircuit<N>,
        window: usize,
        points: &[Point<VarBig<N>>],
        scalars: &[Self::Scalar],
    ) -> Point<VarBig<N>> {
        let n_rounds = C::Scalar::num_bits();
        let person = "ecc-gadget-msm-var-horizontal";

        // Generate deterministic aux points for each chunk of points
        let aux = points
            .chunks(window)
            .enumerate()
            .map(|(chunk_idx, _)| C::hash_to_curve(format!("{person}-{chunk_idx}").as_str(), &[]))
            .collect_vec();
        // Emulate the multiplicaion and find the effective aux contribution
        let aux_sum = C::sum(&aux);
        let correction = (0..n_rounds).fold(C::identity(), |acc, _| acc.double() + aux_sum);
        let correction = self.get_constant(ac, &correction);

        // example table for window = 3 ie chunk_size = 3
        // A
        // A + P_0
        // A + P_1
        // A + P_0 + P_1
        // A + P_2
        // A + P_0 + P_2
        // A + P_1 + P_2
        // A + P_0 + P_1 + P_2
        let tables = points
            .chunks(window)
            .zip_eq(aux)
            .map(|(chunk, aux)| {
                let round_aux = self.get_constant(ac, &aux);

                let mut table = vec![round_aux.clone()];
                chunk.iter().enumerate().for_each(|(i, point)| {
                    (0..(1 << i))
                        .for_each(|j| table.push(self.add_incomplete(ac, &table[j], point)))
                });

                table
            })
            .collect_vec();

        // Decompose scalars into bits
        let scalars = scalars
            .iter()
            .map(|scalar| {
                let mut scalar = self.decompose_scalar(ac, 1, scalar).unwrap();
                scalar.reverse();
                scalar
            })
            .collect_vec();

        let mut acc = None;
        for round in 0..(C::Scalar::num_bits()) {
            if let Some(acc) = acc.as_mut() {
                *acc = self.double_incomplete(ac, acc);
            }

            let add_chain = tables
                .iter()
                .zip_eq(scalars.chunks(window))
                .map(|(table, scalars)| {
                    assert_eq!(table.len(), 1 << scalars.len());
                    let selector = scalars.iter().map(|scalar| scalar[round]).collect_vec();
                    self.select_from_table(ac, &selector, table).unwrap()
                })
                .chain(acc)
                .collect_vec();

            acc = Some(self.add_chain(ac, &add_chain));
        }
        self.sub_incomplete(ac, &acc.unwrap(), &correction)
    }

    // Warning: each set of points must be assigned to a different memory segment
    fn msm_var_horizontal_with_mem(
        &self,
        ac: &mut AbstractCircuit<N>,
        window: usize,
        points: &[Point<VarBig<N>>],
        scalars: &[Self::Scalar],
    ) -> Point<VarBig<N>> {
        let n_rounds = C::Scalar::num_bits();
        let person = "ecc-gadget-msm-var-horizontal";

        // Generate deterministic aux points for each chunk of points
        let aux = points
            .chunks(window)
            .enumerate()
            .map(|(chunk_idx, _)| C::hash_to_curve(format!("{person}-{chunk_idx}").as_str(), &[]))
            .collect_vec();
        // Emulate the multiplicaion and find the effective aux contribution
        let aux_sum = C::sum(&aux);
        let correction = (0..n_rounds).fold(C::identity(), |acc, _| acc.double() + aux_sum);
        let correction = self.get_constant(ac, &correction);

        let table_size = 1 << window;
        let mem_segment = points
            .chunks(window)
            .zip_eq(aux)
            .map(|(chunk, aux)| {
                // Get unique memory segment for this point
                let mem_segment = ac.wo_mem_ir.next_segment();

                // example table for window = 3
                // A
                // A + P_0
                // A + P_1
                // A + P_0 + P_1
                // A + P_2
                // A + P_0 + P_2
                // A + P_1 + P_2
                // A + P_0 + P_1 + P_2

                let round_aux = self.get_constant(ac, &aux);
                let mut table = vec![round_aux.clone()];
                self.write(
                    ac,
                    mem_segment,
                    N::zero(),
                    table_size,
                    table.last().unwrap(),
                )
                .unwrap();

                chunk.iter().enumerate().for_each(|(i, point)| {
                    let b = 1 << i;
                    (0..b).for_each(|j| {
                        let address = N::from_u64((b + j) as u64);
                        table.push(self.add_incomplete(ac, &table[j], point));
                        self.write(ac, mem_segment, address, table_size, table.last().unwrap())
                            .unwrap();
                    });
                });
                mem_segment
            })
            .collect_vec();

        let scalars = scalars
            .iter()
            .map(|scalar| {
                let mut scalar = self.decompose_scalar(ac, 1, scalar).unwrap();
                scalar.reverse();
                scalar
            })
            .collect_vec();

        let mut acc = None;
        for round in 0..(C::Scalar::num_bits()) {
            if let Some(acc) = acc.as_mut() {
                *acc = self.double_incomplete(ac, acc);
            }

            let add_chain = scalars
                .chunks(window)
                .zip_eq(mem_segment.iter())
                .map(|(scalars, mem_segment)| {
                    // Recover table index
                    let coeffs = scalars.iter().map(|e| e[round]).collect_vec();
                    let table_index = &ac.horner(&coeffs, N::from_u64(2));
                    // Get the point from the table
                    self.read(ac, *mem_segment, N::zero(), table_index, table_size)
                        .unwrap()
                })
                .chain(acc)
                .collect_vec();

            acc = Some(self.add_chain(ac, &add_chain));
        }
        self.sub_incomplete(ac, &acc.unwrap(), &correction)
    }
}
