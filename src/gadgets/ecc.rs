//! This module implements various elliptic curve gadgets
#![allow(non_snake_case)]
use crate::gadgets::utils::{
  alloc_one, alloc_zero, conditionally_select, conditionally_select2, select_one_or, select_zero_or,
};
use bellperson::{
  gadgets::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    Assignment,
  },
  ConstraintSystem, SynthesisError,
};
use ff::PrimeField;

/// AllocatedPoint provides an elliptic curve abstraction inside a circuit.
#[derive(Clone)]
pub struct AllocatedPoint<Fp>
where
  Fp: PrimeField,
{
  pub(crate) x: AllocatedNum<Fp>,
  pub(crate) y: AllocatedNum<Fp>,
  pub(crate) is_infinity: AllocatedNum<Fp>,
}

impl<Fp> AllocatedPoint<Fp>
where
  Fp: PrimeField,
{
  /// Allocates a new point on the curve using coordinates provided by `coords`.
  pub fn alloc<CS>(mut cs: CS, coords: Option<(Fp, Fp, bool)>) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<Fp>,
  {
    let x = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(coords.unwrap().0))?;
    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(coords.unwrap().1))?;
    let is_infinity = AllocatedNum::alloc(cs.namespace(|| "is_infinity"), || {
      Ok(if coords.unwrap().2 {
        Fp::one()
      } else {
        Fp::zero()
      })
    })?;
    cs.enforce(
      || "is_infinity is bit",
      |lc| lc + is_infinity.get_variable(),
      |lc| lc + CS::one() - is_infinity.get_variable(),
      |lc| lc,
    );

    Ok(AllocatedPoint { x, y, is_infinity })
  }

  /// Allocates a default point on the curve.
  pub fn default<CS>(mut cs: CS) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<Fp>,
  {
    let zero = alloc_zero(cs.namespace(|| "zero"))?;
    let one = alloc_one(cs.namespace(|| "one"))?;

    Ok(AllocatedPoint {
      x: zero.clone(),
      y: zero,
      is_infinity: one,
    })
  }

  /// Returns coordinates associated with the point.
  pub fn get_coordinates(&self) -> (&AllocatedNum<Fp>, &AllocatedNum<Fp>, &AllocatedNum<Fp>) {
    (&self.x, &self.y, &self.is_infinity)
  }

  // Allocate a random point. Only used for testing
  #[cfg(test)]
  pub fn random_vartime<CS: ConstraintSystem<Fp>>(mut cs: CS) -> Result<Self, SynthesisError> {
    loop {
      let x = Fp::random(&mut OsRng);
      let y = (x * x * x + Fp::one() + Fp::one() + Fp::one() + Fp::one() + Fp::one()).sqrt();
      if y.is_some().unwrap_u8() == 1 {
        let x_alloc = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(x))?;
        let y_alloc = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(y.unwrap()))?;
        let is_infinity = alloc_zero(cs.namespace(|| "Is Infinity"))?;
        return Ok(Self {
          x: x_alloc,
          y: y_alloc,
          is_infinity,
        });
      }
    }
  }

  // Make the point io
  #[cfg(test)]
  pub fn inputize<CS: ConstraintSystem<Fp>>(&self, mut cs: CS) -> Result<(), SynthesisError> {
    let _ = self.x.inputize(cs.namespace(|| "Input point.x"));
    let _ = self.y.inputize(cs.namespace(|| "Input point.y"));
    let _ = self
      .is_infinity
      .inputize(cs.namespace(|| "Input point.is_infinity"));
    Ok(())
  }

  /// Adds other point to this point and returns the result
  /// Assumes that both other.is_infinity and this.is_infinty are bits
  pub fn add<CS: ConstraintSystem<Fp>>(
    &self,
    mut cs: CS,
    other: &AllocatedPoint<Fp>,
  ) -> Result<Self, SynthesisError> {
    // Allocate the boolean variables that check if either of the points is infinity

    //************************************************************************/
    // lambda = (other.y - self.y) * (other.x - self.x).invert().unwrap();
    //************************************************************************/
    // First compute (other.x - self.x).inverse()
    // If either self or other are 1 then compute bogus values

    // x_diff = other != inf && self != inf ? (other.x - self.x) : 1
    let x_diff_actual = AllocatedNum::alloc(cs.namespace(|| "actual x diff"), || {
      Ok(*other.x.get_value().get()? - *self.x.get_value().get()?)
    })?;
    cs.enforce(
      || "actual x_diff is correct",
      |lc| lc + other.x.get_variable() - self.x.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + x_diff_actual.get_variable(),
    );

    // Compute self.is_infinity OR other.is_infinity
    let at_least_one_inf = AllocatedNum::alloc(cs.namespace(|| "at least one inf"), || {
      Ok(*self.is_infinity.get_value().get()? * *other.is_infinity.get_value().get()?)
    })?;
    cs.enforce(
      || "at least one inf = self.is_infinity * other.is_infinity",
      |lc| lc + self.is_infinity.get_variable(),
      |lc| lc + other.is_infinity.get_variable(),
      |lc| lc + at_least_one_inf.get_variable(),
    );

    // x_diff = 1 if either self.is_infinity or other.is_infinity else x_diff_actual
    let x_diff = select_one_or(
      cs.namespace(|| "Compute x_diff"),
      &x_diff_actual,
      &at_least_one_inf,
    )?;

    let x_diff_inv = AllocatedNum::alloc(cs.namespace(|| "x diff inverse"), || {
      if *at_least_one_inf.get_value().get()? == Fp::one() {
        // Set to default
        Ok(Fp::one())
      } else {
        // Set to the actual inverse
        let inv = (*other.x.get_value().get()? - *self.x.get_value().get()?).invert();
        if inv.is_some().unwrap_u8() == 1 {
          Ok(inv.unwrap())
        } else {
          Err(SynthesisError::DivisionByZero)
        }
      }
    })?;

    cs.enforce(
      || "Check inverse",
      |lc| lc + x_diff.get_variable(),
      |lc| lc + x_diff_inv.get_variable(),
      |lc| lc + CS::one(),
    );

    let lambda = AllocatedNum::alloc(cs.namespace(|| "lambda"), || {
      Ok(
        (*other.y.get_value().get()? - *self.y.get_value().get()?)
          * x_diff_inv.get_value().get()?,
      )
    })?;
    cs.enforce(
      || "Check that lambda is correct",
      |lc| lc + other.y.get_variable() - self.y.get_variable(),
      |lc| lc + x_diff_inv.get_variable(),
      |lc| lc + lambda.get_variable(),
    );

    //************************************************************************/
    // x = lambda * lambda - self.x - other.x;
    //************************************************************************/
    let x = AllocatedNum::alloc(cs.namespace(|| "x"), || {
      Ok(
        *lambda.get_value().get()? * lambda.get_value().get()?
          - *self.x.get_value().get()?
          - *other.x.get_value().get()?,
      )
    })?;
    cs.enforce(
      || "check that x is correct",
      |lc| lc + lambda.get_variable(),
      |lc| lc + lambda.get_variable(),
      |lc| lc + x.get_variable() + self.x.get_variable() + other.x.get_variable(),
    );

    //************************************************************************/
    // y = lambda * (self.x - x) - self.y;
    //************************************************************************/
    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
      Ok(
        *lambda.get_value().get()? * (*self.x.get_value().get()? - *x.get_value().get()?)
          - *self.y.get_value().get()?,
      )
    })?;

    cs.enforce(
      || "Check that y is correct",
      |lc| lc + lambda.get_variable(),
      |lc| lc + self.x.get_variable() - x.get_variable(),
      |lc| lc + y.get_variable() + self.y.get_variable(),
    );

    let is_infinity = AllocatedNum::alloc(cs.namespace(|| "is infinity"), || Ok(Fp::zero()))?;

    //************************************************************************/
    // We only return the computed x, y if neither of the points is infinity.
    // if self.is_infinity return other.clone()
    // elif other.is_infinity return self.clone()
    // Otherwise return the computed points.
    //************************************************************************/
    // Now compute the output x
    let inner_x = conditionally_select2(
      cs.namespace(|| "final x: inner if"),
      &self.x,
      &x,
      &other.is_infinity,
    )?;
    let x = conditionally_select2(
      cs.namespace(|| "final x: outer if"),
      &other.x,
      &inner_x,
      &self.is_infinity,
    )?;

    // The output y
    let inner_y = conditionally_select2(
      cs.namespace(|| "final y: inner if"),
      &self.y,
      &y,
      &other.is_infinity,
    )?;
    let y = conditionally_select2(
      cs.namespace(|| "final y: outer if"),
      &other.y,
      &inner_y,
      &self.is_infinity,
    )?;

    // The output is_infinity
    let inner_is_infinity = conditionally_select2(
      cs.namespace(|| "final is infinity: inner if"),
      &self.is_infinity,
      &is_infinity,
      &other.is_infinity,
    )?;
    let is_infinity = conditionally_select2(
      cs.namespace(|| "final is infinity: outer if"),
      &other.is_infinity,
      &inner_is_infinity,
      &self.is_infinity,
    )?;
    Ok(Self { x, y, is_infinity })
  }

  /// Doubles the supplied point.
  pub fn double<CS: ConstraintSystem<Fp>>(&self, mut cs: CS) -> Result<Self, SynthesisError> {
    //*************************************************************/
    // lambda = (Fp::one() + Fp::one() + Fp::one())
    //  * self.x
    //  * self.x
    //  * ((Fp::one() + Fp::one()) * self.y).invert().unwrap();
    /*************************************************************/

    // Compute tmp = (Fp::one() + Fp::one())* self.y ? self != inf : 1
    let tmp_actual = AllocatedNum::alloc(cs.namespace(|| "tmp_actual"), || {
      Ok(*self.y.get_value().get()? + *self.y.get_value().get()?)
    })?;
    cs.enforce(
      || "check tmp_actual",
      |lc| lc + CS::one() + CS::one(),
      |lc| lc + self.y.get_variable(),
      |lc| lc + tmp_actual.get_variable(),
    );

    let tmp = select_one_or(cs.namespace(|| "tmp"), &tmp_actual, &self.is_infinity)?;

    // Compute inv = tmp.invert
    let tmp_inv = AllocatedNum::alloc(cs.namespace(|| "tmp inverse"), || {
      if *self.is_infinity.get_value().get()? == Fp::one() {
        // Return default value 1
        Ok(Fp::one())
      } else {
        // Return the actual inverse
        let inv = (*tmp.get_value().get()?).invert();
        if inv.is_some().unwrap_u8() == 1 {
          Ok(inv.unwrap())
        } else {
          Err(SynthesisError::DivisionByZero)
        }
      }
    })?;
    cs.enforce(
      || "Check inverse",
      |lc| lc + tmp.get_variable(),
      |lc| lc + tmp_inv.get_variable(),
      |lc| lc + CS::one(),
    );

    // Now compute lambda as (Fp::one() + Fp::one + Fp::one()) * self.x * self.x * tmp_inv
    let prod_1 = AllocatedNum::alloc(cs.namespace(|| "alloc prod 1"), || {
      Ok(*tmp_inv.get_value().get()? * self.x.get_value().get()?)
    })?;
    cs.enforce(
      || "Check prod 1",
      |lc| lc + self.x.get_variable(),
      |lc| lc + tmp_inv.get_variable(),
      |lc| lc + prod_1.get_variable(),
    );

    let prod_2 = AllocatedNum::alloc(cs.namespace(|| "alloc prod 2"), || {
      Ok(*prod_1.get_value().get()? * self.x.get_value().get()?)
    })?;
    cs.enforce(
      || "Check prod 2",
      |lc| lc + self.x.get_variable(),
      |lc| lc + prod_1.get_variable(),
      |lc| lc + prod_2.get_variable(),
    );

    let lambda = AllocatedNum::alloc(cs.namespace(|| "lambda"), || {
      Ok(*prod_2.get_value().get()? * (Fp::one() + Fp::one() + Fp::one()))
    })?;
    cs.enforce(
      || "Check lambda",
      |lc| lc + CS::one() + CS::one() + CS::one(),
      |lc| lc + prod_2.get_variable(),
      |lc| lc + lambda.get_variable(),
    );

    /*************************************************************/
    //          x = lambda * lambda - self.x - self.x;
    /*************************************************************/

    let x = AllocatedNum::alloc(cs.namespace(|| "x"), || {
      Ok(
        ((*lambda.get_value().get()?) * (*lambda.get_value().get()?))
          - *self.x.get_value().get()?
          - self.x.get_value().get()?,
      )
    })?;
    cs.enforce(
      || "Check x",
      |lc| lc + lambda.get_variable(),
      |lc| lc + lambda.get_variable(),
      |lc| lc + x.get_variable() + self.x.get_variable() + self.x.get_variable(),
    );

    /*************************************************************/
    //        y = lambda * (self.x - x) - self.y;
    /*************************************************************/

    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
      Ok(
        (*lambda.get_value().get()?) * (*self.x.get_value().get()? - x.get_value().get()?)
          - self.y.get_value().get()?,
      )
    })?;
    cs.enforce(
      || "Check y",
      |lc| lc + lambda.get_variable(),
      |lc| lc + self.x.get_variable() - x.get_variable(),
      |lc| lc + y.get_variable() + self.y.get_variable(),
    );

    /*************************************************************/
    // Only return the computed x and y if the point is not infinity
    /*************************************************************/

    // x
    let x = select_zero_or(cs.namespace(|| "final x"), &x, &self.is_infinity)?;

    // y
    let y = select_zero_or(cs.namespace(|| "final y"), &y, &self.is_infinity)?;

    // is_infinity
    let is_infinity = self.is_infinity.clone();

    Ok(Self { x, y, is_infinity })
  }

  /// A gadget for scalar multiplication.
  pub fn scalar_mul<CS: ConstraintSystem<Fp>>(
    &self,
    mut cs: CS,
    scalar: Vec<AllocatedBit>,
  ) -> Result<Self, SynthesisError> {
    let mut res = Self::default(cs.namespace(|| "res"))?;
    for i in (0..scalar.len()).rev() {
      /*************************************************************/
      //  res = res.double();
      /*************************************************************/

      res = res.double(cs.namespace(|| format!("{}: double", i)))?;

      /*************************************************************/
      //  if scalar[i] {
      //    res = self.add(&res);
      //  }
      /*************************************************************/

      let self_and_res = self.add(cs.namespace(|| format!("{}: add", i)), &res)?;
      res = Self::conditionally_select(
        cs.namespace(|| format!("{}: Update res", i)),
        &self_and_res,
        &res,
        &Boolean::from(scalar[i].clone()),
      )?;
    }
    Ok(res)
  }

  /// If condition outputs a otherwise outputs b
  pub fn conditionally_select<CS: ConstraintSystem<Fp>>(
    mut cs: CS,
    a: &Self,
    b: &Self,
    condition: &Boolean,
  ) -> Result<Self, SynthesisError> {
    let x = conditionally_select(cs.namespace(|| "select x"), &a.x, &b.x, condition)?;

    let y = conditionally_select(cs.namespace(|| "select y"), &a.y, &b.y, condition)?;

    let is_infinity = conditionally_select(
      cs.namespace(|| "select is_infinity"),
      &a.is_infinity,
      &b.is_infinity,
      condition,
    )?;

    Ok(Self { x, y, is_infinity })
  }
}

#[cfg(test)]
use ff::PrimeFieldBits;
#[cfg(test)]
use rand_latest::rngs::OsRng;
#[cfg(test)]
use std::marker::PhantomData;

#[cfg(test)]
#[derive(Debug, Clone)]
pub struct Point<Fp>
where
  Fp: PrimeField + PrimeFieldBits,
{
  x: Fp,
  y: Fp,
  is_infinity: bool,
}

#[cfg(test)]
impl<Fp> Point<Fp>
where
  Fp: PrimeField + PrimeFieldBits,
{
  pub fn new(x: Fp, y: Fp, is_infinity: bool) -> Self {
    Self {
      x,
      y,
      is_infinity,
    }
  }

  pub fn random_vartime() -> Self {
    loop {
      let x = Fp::random(&mut OsRng);
      let y = (x * x * x + Fp::one() + Fp::one() + Fp::one() + Fp::one() + Fp::one()).sqrt();
      if y.is_some().unwrap_u8() == 1 {
        return Self {
          x,
          y: y.unwrap(),
          is_infinity: false,
        };
      }
    }
  }

  pub fn add(&self, other: &Point<Fp>) -> Self {
    if self.is_infinity {
      return other.clone();
    }

    if other.is_infinity {
      return self.clone();
    }

    let lambda = (other.y - self.y) * (other.x - self.x).invert().unwrap();
    let x = lambda * lambda - self.x - other.x;
    let y = lambda * (self.x - x) - self.y;
    Self {
      x,
      y,
      is_infinity: false,
    }
  }

  pub fn double(&self) -> Self {
    if self.is_infinity {
      return Self {
        x: Fp::zero(),
        y: Fp::zero(),
        is_infinity: true,
      };
    }

    let lambda = (Fp::one() + Fp::one() + Fp::one())
      * self.x
      * self.x
      * ((Fp::one() + Fp::one()) * self.y).invert().unwrap();
    let x = lambda * lambda - self.x - self.x;
    let y = lambda * (self.x - x) - self.y;
    Self {
      x,
      y,
      is_infinity: false,
    }
  }

  pub fn scalar_mul(&self, scalar: &Fp) -> Self {
    let mut res = Self {
      x: Fp::zero(),
      y: Fp::zero(),
      is_infinity: true,
    };

    let bits = scalar.to_le_bits();
    for i in (0..bits.len()).rev() {
      res = res.double();
      if bits[i] {
        res = self.add(&res);
      }
    }
    res
  }
}

// TODO: Add tests