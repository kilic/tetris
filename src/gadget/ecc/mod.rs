use super::big_field::crt::CrtGadget;
use super::big_field::rns::Range;
use super::big_field::Big;
use crate::gadget::big_field::VarBig;
use crate::ir::ac::AbstractCircuit;
use crate::witness::field::Field;
use crate::witness::Var;
use crate::{Error, Value};
use std::fmt::Debug;

// pub mod bn_pairing;
pub mod bw6;
pub mod compat;
pub mod ecc_base_field;
pub mod ecc_general;
pub mod ecdsa;
pub mod msm;
#[cfg(test)]
pub(crate) mod test;

pub use compat::Curve;

#[derive(Clone, Copy, Debug)]
pub struct Point<N> {
    x: N,
    y: N,
}

pub trait Coordinates {
    type Base;
    fn x(&self) -> &Self::Base;
    fn y(&self) -> &Self::Base;
}

impl<N> Point<N> {
    pub fn new(x: N, y: N) -> Self {
        Point { x, y }
    }
    pub fn unzip(self) -> (N, N) {
        (self.x, self.y)
    }
}

impl<N> Coordinates for Point<N> {
    type Base = N;
    fn x(&self) -> &Self::Base {
        &self.x
    }
    fn y(&self) -> &Self::Base {
        &self.y
    }
}

impl<N: Field> Point<VarBig<N>> {
    pub fn value<C: Curve>(&self) -> Value<C> {
        let x = self.x.cast::<C::Base>().unwrap();
        let y = self.y.cast::<C::Base>().unwrap();
        x.zip(y).map(|(x, y)| C::from_coords(&x, &y).unwrap())
    }
}

pub trait EccGadget<C: Curve, N: Field> {
    type Scalar;

    fn base_field_crt(&self) -> &CrtGadget<N>;

    fn b(&self) -> &Big<N>;

    fn assign_scalar(&self, ac: &mut AbstractCircuit<N>, scalar: &Value<C::Scalar>)
        -> Self::Scalar;

    fn decompose_scalar(
        &self,
        ac: &mut AbstractCircuit<N>,
        window: usize,
        scalar: &Self::Scalar,
    ) -> Result<Vec<Var<N>>, Error>;

    fn constant_point(&self, point: &C) -> Point<Big<N>> {
        let ch = self.base_field_crt();
        let (x, y) = point.coords().unzip();
        let x = ch.rns.big_from_uint(&x.uint());
        let y = ch.rns.big_from_uint(&y.uint());
        Point::new(x, y)
    }

    fn get_constant(&self, ac: &mut AbstractCircuit<N>, point: &C) -> Point<VarBig<N>> {
        let ch = self.base_field_crt();
        let (x, y) = point.coords().unzip();
        let x = ch.get_constant(ac, &x.uint()).unwrap();
        let y = ch.get_constant(ac, &y.uint()).unwrap();
        Point::new(x, y)
    }

    fn assign_point(
        &self,
        ac: &mut AbstractCircuit<N>,
        point: &Value<C>,
    ) -> Result<Point<VarBig<N>>, Error> {
        let ch = self.base_field_crt();
        let (x, y) = point
            .map(|point| {
                let (x, y) = point.coords().unzip();
                (x.uint(), y.uint())
            })
            .unzip();
        let x = ch.assign(ac, x.as_ref(), &Range::Remainder)?;
        let y = ch.assign(ac, y.as_ref(), &Range::Remainder)?;
        let point = Point::new(x, y);
        self.assert_on_curve(ac, &point)?;
        Ok(point)
    }

    fn write(
        &self,
        ac: &mut AbstractCircuit<N>,
        segment: N,
        address: N,
        y_offset: usize,
        point: &Point<VarBig<N>>,
    ) -> Result<(), Error> {
        let ch = self.base_field_crt();
        let y_offset = N::from_u64(y_offset as u64);
        ch.write(ac, segment, address, point.x())?;
        ch.write(ac, segment, address + y_offset, point.y())?;
        Ok(())
    }

    fn read(
        &self,
        ac: &mut AbstractCircuit<N>,
        segment: N,
        address_offset: N,
        address_fine: &Var<N>,
        y_offset: usize,
    ) -> Result<Point<VarBig<N>>, Error> {
        let ch = self.base_field_crt();
        let y_offset = N::from_u64(y_offset as u64);
        let x = &ch.read(ac, segment, address_offset, address_fine)?;
        let y = &ch.read(ac, segment, address_offset + y_offset, address_fine)?;
        ac.sanity_ok(|| {
            x.big().zip(y.big()).maybe(|(x, y)| {
                let x = x.cast::<C::Base>().ok();
                let y = y.cast::<C::Base>().ok();
                x.zip(y).and_then(|(x, y)| C::from_coords(&x, &y))
            })
        })?;
        Ok(Point::new(x.clone(), y.clone()))
    }

    fn write_constant(
        &self,
        ac: &mut AbstractCircuit<N>,
        mem_segment: N,
        address: N,
        y_offset: usize,
        point: &C,
    ) -> Result<(), Error> {
        let ch = self.base_field_crt();
        let point = self.constant_point(point);
        let y_offset = N::from_u64(y_offset as u64);
        ch.write_constant(ac, mem_segment, address, point.x())?;
        ch.write_constant(ac, mem_segment, address + y_offset, point.y())?;
        Ok(())
    }

    fn read_constant(
        &self,
        ac: &mut AbstractCircuit<N>,
        mem_segment: N,
        address_offset: N,
        address_fine: &Var<N>,
        y_offset: usize,
    ) -> Result<Point<VarBig<N>>, Error> {
        let ch = self.base_field_crt();
        let y_offset = N::from_u64(y_offset as u64);
        let x = &ch.read_constant(ac, mem_segment, address_offset, address_fine)?;
        let y = &ch.read_constant(ac, mem_segment, address_offset + y_offset, address_fine)?;

        ac.sanity_ok(|| {
            x.uint().zip(y.uint()).maybe(|(x, y)| {
                let x = C::Base::from_uint(x).ok();
                let y = C::Base::from_uint(y).ok();
                x.zip(y).and_then(|(x, y)| C::from_coords(&x, &y))
            })
        })?;

        Ok(Point::new(x.clone(), y.clone()))
    }

    fn assert_on_curve(
        &self,
        ac: &mut AbstractCircuit<N>,
        point: &Point<VarBig<N>>,
    ) -> Result<(), Error> {
        let ch = self.base_field_crt();
        let y_square = &ch.square(ac, point.y(), &[], &[]);
        let x_square = &ch.square(ac, point.x(), &[], &[]);
        let x_cube = &ch.mul(ac, point.x(), x_square, &[], &[]);
        let x_cube_b = &x_cube.add_constant(ac, self.b());
        ch.normal_equal(ac, x_cube_b, y_square)
    }

    fn is_on_curve(&self, ac: &mut AbstractCircuit<N>, point: &Point<VarBig<N>>) -> Var<N> {
        let ch = self.base_field_crt();
        let y_square = &ch.square(ac, point.y(), &[], &[]);
        let x_square = &ch.square(ac, point.x(), &[], &[]);
        let x_cube = &ch.mul(ac, point.x(), x_square, &[], &[]);
        let x_cube_b = &x_cube.add_constant(ac, self.b());
        ch.is_equal(ac, x_cube_b, y_square)
    }

    fn copy_equal(
        &self,
        ac: &mut AbstractCircuit<N>,
        p0: &Point<VarBig<N>>,
        p1: &Point<VarBig<N>>,
    ) -> Result<(), Error> {
        p0.x().copy_equal(ac, p1.x())?;
        p0.y().copy_equal(ac, p1.y())?;
        Ok(())
    }

    fn normal_equal(
        &self,
        ac: &mut AbstractCircuit<N>,
        p0: &Point<VarBig<N>>,
        p1: &Point<VarBig<N>>,
    ) -> Result<(), Error> {
        let ch = self.base_field_crt();
        ch.normal_equal(ac, p0.x(), p1.x())?;
        ch.normal_equal(ac, p0.y(), p1.y())?;
        Ok(())
    }

    fn normalize(&self, ac: &mut AbstractCircuit<N>, point: &Point<VarBig<N>>) -> Point<VarBig<N>> {
        let ch = self.base_field_crt();
        let x = ch.reduce(ac, point.x());
        let y = ch.reduce(ac, point.y());
        Point::new(x, y)
    }

    fn select(
        &self,
        ac: &mut AbstractCircuit<N>,
        c: &Var<N>,
        p0: &Point<VarBig<N>>,
        p1: &Point<VarBig<N>>,
    ) -> Result<Point<VarBig<N>>, Error> {
        let x = p0.x().select(ac, c, p1.x())?;
        let y = p0.y().select(ac, c, p1.y())?;
        Ok(Point::new(x, y))
    }

    fn select_from_table(
        &self,
        ac: &mut AbstractCircuit<N>,
        selector: &[Var<N>],
        table: &[Point<VarBig<N>>],
    ) -> Result<Point<VarBig<N>>, Error> {
        let ch = self.base_field_crt();
        let x_table = table.iter().map(|p| p.x().clone()).collect::<Vec<_>>();
        let y_table = table.iter().map(|p| p.y().clone()).collect::<Vec<_>>();
        let x = ch.select_from_table(ac, selector, &x_table)?;
        let y = ch.select_from_table(ac, selector, &y_table)?;
        Ok(Point::new(x, y))
    }

    fn select_from_constant_table(
        &self,
        ac: &mut AbstractCircuit<N>,
        selector: &[Var<N>],
        table: &[Point<Big<N>>],
    ) -> Result<Point<VarBig<N>>, Error> {
        let ch = self.base_field_crt();
        let x_table = table.iter().map(|p| p.x().clone()).collect::<Vec<_>>();
        let y_table = table.iter().map(|p| p.y().clone()).collect::<Vec<_>>();
        let x = ch.select_from_constant_table(ac, selector, &x_table)?;
        let y = ch.select_from_constant_table(ac, selector, &y_table)?;
        Ok(Point::new(x, y))
    }

    fn add_incomplete(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &Point<VarBig<N>>,
        b: &Point<VarBig<N>>,
    ) -> Point<VarBig<N>> {
        let ch = self.base_field_crt();
        // lambda = b_y - a_y / b_x - a_x
        let numer = &b.y.sub(ac, &a.y);
        let denom = &b.x.sub(ac, &a.x);
        let lambda = &ch.div(ac, numer, denom);
        // c_x =  lambda * lambda - a_x - b_x
        let x = ch.square(ac, lambda, &[], &[&a.x, &b.x]);
        // c_y = lambda * (a_x - c_x) - a_y
        let t = &a.x.sub(ac, &x);
        let y = ch.mul(ac, t, lambda, &[], &[&a.y]);
        Point::new(x, y)
    }

    fn sub_incomplete(
        &self,
        ac: &mut AbstractCircuit<N>,
        a: &Point<VarBig<N>>,
        b: &Point<VarBig<N>>,
    ) -> Point<VarBig<N>> {
        let ch = self.base_field_crt();
        // lambda = b_y + a_y / b_x - a_x
        let numer = &b.y.add(ac, &a.y);
        let denom = &a.x.sub(ac, &b.x);
        let lambda = &ch.div(ac, numer, denom);
        // c_x =  lambda * lambda - a_x - b_x
        let x = ch.square(ac, lambda, &[], &[&a.x, &b.x]);
        // c_y = lambda * (a_x - c_x) - a_y
        let t = &a.x.sub(ac, &x);
        let y = ch.mul(ac, t, lambda, &[], &[&a.y]);
        Point::new(x, y)
    }

    fn double_incomplete(
        &self,
        ac: &mut AbstractCircuit<N>,
        point: &Point<VarBig<N>>,
    ) -> Point<VarBig<N>> {
        let ch = self.base_field_crt();
        // lambda = (3 * a_x^2) / 2 * a_y
        let x_square = &ch.square(ac, &point.x, &[], &[]);
        let numer = &x_square.triple(ac);
        let denom = &point.y.double(ac);
        let lambda = &ch.div(ac, numer, denom);
        // c_x = lambda * lambda - 2 * a_x
        let x = ch.square(ac, lambda, &[], &[&point.x, &point.x]);
        // c_y = lambda * (a_x - c_x) - a_y
        let t = &point.x.sub(ac, &x);
        let y = ch.mul(ac, lambda, t, &[], &[&point.y]);
        Point::new(x, y)
    }

    // ported from barretenberg
    // https://github.com/AztecProtocol/barretenberg/blob/master/cpp/src/barretenberg/stdlib/primitives/biggroup/biggroup_impl.hpp
    fn add_chain(
        &self,
        ac: &mut AbstractCircuit<N>,
        points: &[Point<VarBig<N>>],
    ) -> Point<VarBig<N>> {
        let ch = self.base_field_crt();

        assert!(!points.is_empty());
        if points.len() == 1 {
            return points[0].clone();
        }

        struct State<N: Field> {
            x_prev: VarBig<N>,
            y_prev: VarBig<N>,
            x_cur: VarBig<N>,
            lambda: VarBig<N>,
        }

        let p0 = &points[0];
        let p1 = &points[1];

        let t0 = &p0.y.sub(ac, &p1.y);
        let t1 = &p1.x.sub(ac, &p0.x);
        let lambda = ch.div(ac, t0, t1);
        // let lambda = ch.neg(ac, &lambda);
        let x_cur = ch.square(ac, &lambda, &[], &[&p1.x, &p0.x]);
        let mut state = State {
            x_prev: p0.x.clone(),
            y_prev: p0.y.clone(),
            x_cur,
            lambda,
        };

        for point in points.iter().skip(2) {
            let t = &state.x_prev.sub(ac, &state.x_cur);
            let denom = &state.x_cur.sub(ac, &point.x);
            let lambda = ch.mul_div(ac, &state.lambda, t, denom, &[&point.y, &state.y_prev], &[]);
            // let lambda = ch.neg(ac, &lambda);
            state.x_cur = ch.square(ac, &lambda, &[], &[&state.x_cur, &point.x]);
            state.lambda = lambda;
            state.x_prev = point.x.clone();
            state.y_prev = point.y.clone();
        }
        let t = &state.x_cur.sub(ac, &state.x_prev);
        let y_cur = ch.mul(ac, &state.lambda, t, &[], &[&state.y_prev]);
        Point::new(state.x_cur, y_cur)
    }
}
