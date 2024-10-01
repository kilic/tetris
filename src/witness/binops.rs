use crate::{Field, QuadScaled, Scaled, Var};

impl<F: Field> std::ops::Neg for Var<F> {
    type Output = Scaled<F>;
    fn neg(self) -> Self::Output {
        Scaled {
            var: self,
            coeff: -F::one(),
        }
    }
}

impl<'a, F: Field> std::ops::Neg for &'a Var<F> {
    type Output = Scaled<F>;
    fn neg(self) -> Self::Output {
        Scaled {
            var: *self,
            coeff: -F::one(),
        }
    }
}

impl<F: Field> std::ops::Neg for Scaled<F> {
    type Output = Scaled<F>;
    fn neg(self) -> Self::Output {
        Scaled {
            var: self.var,
            coeff: self.coeff.neg(),
        }
    }
}

impl<'a, F: Field> std::ops::Neg for &'a Scaled<F> {
    type Output = Scaled<F>;
    fn neg(self) -> Self::Output {
        Scaled {
            var: self.var,
            coeff: self.coeff.neg(),
        }
    }
}

impl<F: Field> std::ops::Neg for QuadScaled<F> {
    type Output = QuadScaled<F>;
    fn neg(self) -> Self::Output {
        QuadScaled {
            var: self.var,
            coeff: self.coeff.neg(),
        }
    }
}

impl<'a, F: Field> std::ops::Neg for &'a QuadScaled<F> {
    type Output = QuadScaled<F>;
    fn neg(self) -> Self::Output {
        QuadScaled {
            var: self.var,
            coeff: self.coeff.neg(),
        }
    }
}

// F X Var = Scaled

impl<F: Field> std::ops::Mul<&F> for &Var<F> {
    type Output = Scaled<F>;
    fn mul(self, rhs: &F) -> Self::Output {
        Scaled::new(self, *rhs)
    }
}

impl<F: Field> std::ops::Mul<F> for &Var<F> {
    type Output = Scaled<F>;
    fn mul(self, rhs: F) -> Self::Output {
        self.mul(&rhs)
    }
}

impl<F: Field> std::ops::Mul<&F> for Var<F> {
    type Output = Scaled<F>;
    fn mul(self, rhs: &F) -> Self::Output {
        self.as_ref().mul(rhs)
    }
}

impl<F: Field> std::ops::Mul<F> for Var<F> {
    type Output = Scaled<F>;
    fn mul(self, rhs: F) -> Self::Output {
        self.mul(&rhs)
    }
}

// Var X Var = QuadScaled

impl<F: Field> std::ops::Mul for &Var<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: &Var<F>) -> Self::Output {
        QuadScaled::new(self, rhs, F::one())
    }
}

impl<F: Field> std::ops::Mul<Var<F>> for &Var<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: Var<F>) -> Self::Output {
        self.mul(&rhs)
    }
}

impl<F: Field> std::ops::Mul<&Var<F>> for Var<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: &Var<F>) -> Self::Output {
        self.as_ref().mul(rhs)
    }
}

impl<F: Field> std::ops::Mul for Var<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: Var<F>) -> Self::Output {
        self.mul(&rhs)
    }
}

// Scaled X Var = QuadScaled

impl<F: Field> std::ops::Mul<&Scaled<F>> for &Var<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: &Scaled<F>) -> Self::Output {
        QuadScaled::new(self, &rhs.var, rhs.coeff)
    }
}

impl<F: Field> std::ops::Mul<Scaled<F>> for &Var<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: Scaled<F>) -> Self::Output {
        self.mul(&rhs)
    }
}

impl<F: Field> std::ops::Mul<&Scaled<F>> for Var<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: &Scaled<F>) -> Self::Output {
        self.as_ref().mul(rhs)
    }
}

impl<F: Field> std::ops::Mul<Scaled<F>> for Var<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: Scaled<F>) -> Self::Output {
        self.mul(&rhs)
    }
}

// Var X Scaled = QuadScaled

impl<F: Field> std::ops::Mul<&Var<F>> for &Scaled<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: &Var<F>) -> Self::Output {
        QuadScaled::new(rhs, &self.var, self.coeff)
    }
}

impl<F: Field> std::ops::Mul<Var<F>> for &Scaled<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: Var<F>) -> Self::Output {
        self.mul(&rhs)
    }
}

impl<F: Field> std::ops::Mul<&Var<F>> for Scaled<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: &Var<F>) -> Self::Output {
        self.as_ref().mul(rhs)
    }
}

impl<F: Field> std::ops::Mul<Var<F>> for Scaled<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: Var<F>) -> Self::Output {
        self.mul(&rhs)
    }
}

// Var X Scaled = QuadScaled

impl<F: Field> std::ops::Mul<&Scaled<F>> for &Scaled<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: &Scaled<F>) -> Self::Output {
        QuadScaled::new(&rhs.var, &self.var, self.coeff * rhs.coeff)
    }
}

impl<F: Field> std::ops::Mul<Scaled<F>> for &Scaled<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: Scaled<F>) -> Self::Output {
        self.mul(&rhs)
    }
}

impl<F: Field> std::ops::Mul<&Scaled<F>> for Scaled<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: &Scaled<F>) -> Self::Output {
        self.as_ref().mul(rhs)
    }
}

impl<F: Field> std::ops::Mul<Scaled<F>> for Scaled<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: Scaled<F>) -> Self::Output {
        self.mul(&rhs)
    }
}

// Scaled X F = Scaled

impl<F: Field> std::ops::Mul<&F> for &Scaled<F> {
    type Output = Scaled<F>;
    fn mul(self, rhs: &F) -> Self::Output {
        Scaled::new(&self.var, self.coeff * *rhs)
    }
}

impl<F: Field> std::ops::Mul<F> for &Scaled<F> {
    type Output = Scaled<F>;
    fn mul(self, rhs: F) -> Self::Output {
        self.mul(&rhs)
    }
}

impl<F: Field> std::ops::Mul<&F> for Scaled<F> {
    type Output = Scaled<F>;
    fn mul(self, rhs: &F) -> Self::Output {
        self.as_ref().mul(rhs)
    }
}

impl<F: Field> std::ops::Mul<F> for Scaled<F> {
    type Output = Scaled<F>;
    fn mul(self, rhs: F) -> Self::Output {
        self.mul(&rhs)
    }
}

// QuadScaled X F = QuadScaled

impl<F: Field> std::ops::Mul<&F> for &QuadScaled<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: &F) -> Self::Output {
        QuadScaled::new(self.var0(), self.var1(), self.coeff * *rhs)
    }
}

impl<F: Field> std::ops::Mul<F> for &QuadScaled<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: F) -> Self::Output {
        self.mul(&rhs)
    }
}

impl<F: Field> std::ops::Mul<&F> for QuadScaled<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: &F) -> Self::Output {
        self.as_ref().mul(rhs)
    }
}

impl<F: Field> std::ops::Mul<F> for QuadScaled<F> {
    type Output = QuadScaled<F>;
    fn mul(self, rhs: F) -> Self::Output {
        self.mul(&rhs)
    }
}
