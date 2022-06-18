//! This module implements various elliptic curve gadgets
#![allow(non_snake_case)]
use crate::gadgets::utils::{
  alloc_one, alloc_zero, conditionally_select,
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

/// AllocatedPointTwist provides an elliptic curve abstraction inside a circuit.
#[derive(Clone)]
pub struct AllocatedPointTwist<Fp>
where
  Fp: PrimeField,
{
  pub(crate) x: AllocatedNum<Fp>,
  pub(crate) y: AllocatedNum<Fp>,
  pub(crate) is_infinity: AllocatedNum<Fp>,
}

impl<Fp> AllocatedPointTwist<Fp>
where
  Fp: PrimeField<Repr = [u8; 32]>,
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

    Ok(AllocatedPointTwist { x, y, is_infinity })
  }

  /// Allocates a default point on the curve.
  pub fn default<CS>(mut cs: CS) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<Fp>,
  {
    let zero = alloc_zero(cs.namespace(|| "zero"))?;
    let one = alloc_one(cs.namespace(|| "one"))?;

    Ok(AllocatedPointTwist {
      x: zero.clone(),
      y: one.clone(),
      is_infinity: one,
    })
  }

  /// Returns coordinates associated with the point.
  pub fn get_coordinates(&self) -> (&AllocatedNum<Fp>, &AllocatedNum<Fp>, &AllocatedNum<Fp>) {
    (&self.x, &self.y, &self.is_infinity)
  }

  // Allocate a random point. Only used for testing
  #[cfg(test)]
  pub fn random_vartime<CS: ConstraintSystem<Fp>>(
    mut cs: CS,
    d: Fp,
  ) -> Result<Self, SynthesisError> {
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
    other: &AllocatedPointTwist<Fp>,
  ) -> Result<Self, SynthesisError> {
    // Allocate the boolean variables that check if either of the points is infinity

    //************************************************************************/
    //xv = self.X * other.Y;
    //************************************************************************/
    let xv = AllocatedNum::alloc(cs.namespace(|| "xv"), || {
      Ok(*self.x.get_value().get()? * *other.y.get_value().get()?)
    })?;
    cs.enforce(
      || "xv is correct",
      |lc| lc + self.x.get_variable(),
      |lc| lc + other.y.get_variable(),
      |lc| lc + xv.get_variable(),
    );

    //************************************************************************/
    // yu = self.Y * other.X;
    //************************************************************************/
    let yu = AllocatedNum::alloc(cs.namespace(|| "yu"), || {
      Ok(*self.y.get_value().get()? * other.x.get_value().get()?)
    })?;
    cs.enforce(
      || "check that yu is correct",
      |lc| lc + self.y.get_variable(),
      |lc| lc + other.x.get_variable(),
      |lc| lc + yu.get_variable(),
    );

    //************************************************************************/
    // px = xv + yu;
    //************************************************************************/
    let px = AllocatedNum::alloc(cs.namespace(|| "px"), || {
      Ok(*xv.get_value().get()? + *yu.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that px is correct",
      |lc| lc + xv.get_variable() + yu.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + px.get_variable(),
    );

    //************************************************************************/
    // xu = self.X * other.X;
    //************************************************************************/
    let xu = AllocatedNum::alloc(cs.namespace(|| "xu"), || {
      Ok(*self.x.get_value().get()? * *other.x.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that xu is correct",
      |lc| lc + self.x.get_variable(),
      |lc| lc + other.x.get_variable(),
      |lc| lc + xu.get_variable(),
    );

    //************************************************************************/
    // yv = self.Y * other.Y;
    //************************************************************************/
    let yv = AllocatedNum::alloc(cs.namespace(|| "yv"), || {
      Ok(*self.y.get_value().get()? * *other.y.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that yv is correct",
      |lc| lc + self.y.get_variable(),
      |lc| lc + other.y.get_variable(),
      |lc| lc + yv.get_variable(),
    );

    //************************************************************************/
    // py = yv + xu;
    //************************************************************************/
    let py = AllocatedNum::alloc(cs.namespace(|| "py"), || {
      Ok(*yv.get_value().get()? + *xu.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that py is correct",
      |lc| lc + yv.get_variable() + xu.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + py.get_variable(),
    );

    //************************************************************************/
    // dxyuv = xv * yu * constants::EDWARDS_D;
    //************************************************************************/
    let xyuv = AllocatedNum::alloc(cs.namespace(|| "xyuv"), || {
      Ok(*xv.get_value().get()? * *yu.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that xyuv is correct",
      |lc| lc + xv.get_variable(),
      |lc| lc + yu.get_variable(),
      |lc| lc + xyuv.get_variable(),
    );

    let d = AllocatedNum::alloc(cs.namespace(|| "d"), || {
      Ok(Fp::from_repr(EDWARDS_D.to_repr()).unwrap())
    })?;

    let dxyuv = AllocatedNum::alloc(cs.namespace(|| "dxyuv"), || {
      Ok(*xyuv.get_value().get()? * *d.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that dxyuv is correct",
      |lc| lc + xyuv.get_variable(),
      |lc| lc + d.get_variable(),
      |lc| lc + dxyuv.get_variable(),
    );

    //************************************************************************/
    // denx = one + dxyuv;
    //************************************************************************/
    let one = alloc_one(cs.namespace(|| "one"))?;

    let denx = AllocatedNum::alloc(cs.namespace(|| "denx"), || {
      Ok(*one.get_value().get()? + *dxyuv.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that denx is correct",
      |lc| lc + CS::one() + dxyuv.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + denx.get_variable(),
    );

    //************************************************************************/
    // deny = one - dxyuv = one + (a * dxyuv); where a = -1 mod l
    //************************************************************************/
    let a = AllocatedNum::alloc(cs.namespace(|| "a"), || {
      Ok(Fp::from_repr(EDWARDS_A.to_repr()).unwrap())
    })?;

    let adxyuv = AllocatedNum::alloc(cs.namespace(|| "adxyuv"), || {
      Ok(*a.get_value().get()? * *dxyuv.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that ad is correct",
      |lc| lc + a.get_variable(),
      |lc| lc + dxyuv.get_variable(),
      |lc| lc + adxyuv.get_variable(),
    );

    let deny = AllocatedNum::alloc(cs.namespace(|| "deny"), || {
      Ok(*one.get_value().get()? + *adxyuv.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that deny is correct",
      |lc| lc + CS::one() + adxyuv.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + deny.get_variable(),
    );

    //************************************************************************/
    // x = px * denx.inverse();
    //************************************************************************/
    let denx_inv = AllocatedNum::alloc(cs.namespace(|| "denx inverse"), || {
      let inv = (*denx.get_value().get()?).invert();
      if inv.is_some().unwrap_u8() == 1 {
        Ok(inv.unwrap())
      } else {
        Err(SynthesisError::DivisionByZero)
      }
    })?;

    cs.enforce(
      || "Check denx inverse",
      |lc| lc + denx.get_variable(),
      |lc| lc + denx_inv.get_variable(),
      |lc| lc + CS::one(),
    );

    let x = AllocatedNum::alloc(cs.namespace(|| "x"), || {
      Ok(*px.get_value().get()? * *denx_inv.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that x is correct",
      |lc| lc + px.get_variable(),
      |lc| lc + denx_inv.get_variable(),
      |lc| lc + x.get_variable(),
    );

    //************************************************************************/
    // y = py * deny.inverse();
    //************************************************************************/
    let deny_inv = AllocatedNum::alloc(cs.namespace(|| "deny inverse"), || {
      let inv = (*deny.get_value().get()?).invert();
      if inv.is_some().unwrap_u8() == 1 {
        Ok(inv.unwrap())
      } else {
        Err(SynthesisError::DivisionByZero)
      }
    })?;

    cs.enforce(
      || "Check deny inverse",
      |lc| lc + deny.get_variable(),
      |lc| lc + deny_inv.get_variable(),
      |lc| lc + CS::one(),
    );

    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
      Ok(*py.get_value().get()? * *deny_inv.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that y is correct",
      |lc| lc + py.get_variable(),
      |lc| lc + deny_inv.get_variable(),
      |lc| lc + y.get_variable(),
    );

    let is_infinity = AllocatedNum::alloc(cs.namespace(|| "is infinity"), || Ok(Fp::zero()))?;

    Ok(Self { x, y, is_infinity })
  }

  /// Doubles the supplied point.
  pub fn double<CS: ConstraintSystem<Fp>>(&self, mut cs: CS) -> Result<Self, SynthesisError> {
    //************************************************************************/
    // xx = self.X * self.X;
    //************************************************************************/
    let xx = AllocatedNum::alloc(cs.namespace(|| "xx"), || {
      Ok(*self.x.get_value().get()? * *self.x.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that xx is correct",
      |lc| lc + self.x.get_variable(),
      |lc| lc + self.x.get_variable(),
      |lc| lc + xx.get_variable(),
    );

    //************************************************************************/
    // yy = self.Y * self.Y;
    //************************************************************************/
    let yy = AllocatedNum::alloc(cs.namespace(|| "yy"), || {
      Ok(*self.y.get_value().get()? * *self.y.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that yy is correct",
      |lc| lc + self.y.get_variable(),
      |lc| lc + self.y.get_variable(),
      |lc| lc + yy.get_variable(),
    );

    //************************************************************************/
    // xy = self.X * self.Y;
    //************************************************************************/
    let xy = AllocatedNum::alloc(cs.namespace(|| "xy"), || {
      Ok(*self.x.get_value().get()? * *self.y.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that xy is correct",
      |lc| lc + self.x.get_variable(),
      |lc| lc + self.y.get_variable(),
      |lc| lc + xy.get_variable(),
    );

    //************************************************************************/
    // denumx = yy - xx = yy + (a * xx);
    //************************************************************************/
    let a = AllocatedNum::alloc(cs.namespace(|| "a"), || {
      Ok(Fp::from_repr(EDWARDS_A.to_repr()).unwrap())
    })?;

    let axx = AllocatedNum::alloc(cs.namespace(|| "axx"), || {
      Ok(*a.get_value().get()? * *xx.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that axx is correct",
      |lc| lc + a.get_variable(),
      |lc| lc + xx.get_variable(),
      |lc| lc + axx.get_variable(),
    );

    let denumx = AllocatedNum::alloc(cs.namespace(|| "denumx"), || {
      Ok(*yy.get_value().get()? + *axx.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that denumx is correct",
      |lc| lc + yy.get_variable() + axx.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + denumx.get_variable(),
    );

    //************************************************************************/
    // two = one + one;
    //************************************************************************/
    let one = alloc_one(cs.namespace(|| "one"))?;
    let two = AllocatedNum::alloc(cs.namespace(|| "two"), || {
      Ok(*one.get_value().get()? + *one.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that two is correct",
      |lc| lc + one.get_variable() + one.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + two.get_variable(),
    );

    //************************************************************************/
    // adenumx = -denumx = a * denumx;
    //************************************************************************/
    let adenumx = AllocatedNum::alloc(cs.namespace(|| "adenumx"), || {
      Ok(*a.get_value().get()? * *denumx.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that adenumx is correct",
      |lc| lc + a.get_variable(),
      |lc| lc + denumx.get_variable(),
      |lc| lc + adenumx.get_variable(),
    );

    //************************************************************************/
    // denumy = -denumx + two = adenumx + two;
    //************************************************************************/
    let denumy = AllocatedNum::alloc(cs.namespace(|| "denumy"), || {
      Ok(*adenumx.get_value().get()? + *two.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that denumy is correct",
      |lc| lc + adenumx.get_variable() + two.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + denumy.get_variable(),
    );

    //************************************************************************/
    // xyxy = xy + xy;
    //************************************************************************/
    let xyxy = AllocatedNum::alloc(cs.namespace(|| "xyxy"), || {
      Ok(*xy.get_value().get()? + *xy.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that xyxy is correct",
      |lc| lc + xy.get_variable() + xy.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + xyxy.get_variable(),
    );

    //************************************************************************/
    // xxyy = xx + yy;
    //************************************************************************/
    let xxyy = AllocatedNum::alloc(cs.namespace(|| "xxyy"), || {
      Ok(*xx.get_value().get()? + *yy.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that xxyy is correct",
      |lc| lc + xx.get_variable() + yy.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + xxyy.get_variable(),
    );

    //************************************************************************/
    // x = xyxy * denumx.inverse();
    //************************************************************************/
    let denumx_inv = AllocatedNum::alloc(cs.namespace(|| "denumx inverse"), || {
      let inv = (*denumx.get_value().get()?).invert();
      if inv.is_some().unwrap_u8() == 1 {
        Ok(inv.unwrap())
      } else {
        Err(SynthesisError::DivisionByZero)
      }
    })?;

    cs.enforce(
      || "Check denumx inverse",
      |lc| lc + denumx.get_variable(),
      |lc| lc + denumx_inv.get_variable(),
      |lc| lc + CS::one(),
    );

    let x = AllocatedNum::alloc(cs.namespace(|| "x"), || {
      Ok(*xyxy.get_value().get()? * *denumx_inv.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that x is correct",
      |lc| lc + xyxy.get_variable(),
      |lc| lc + denumx_inv.get_variable(),
      |lc| lc + x.get_variable(),
    );

    //************************************************************************/
    // y = xxyy * denumy.inverse();
    //************************************************************************/
    let denumy_inv = AllocatedNum::alloc(cs.namespace(|| "denumy inverse"), || {
      let inv = (*denumy.get_value().get()?).invert();
      if inv.is_some().unwrap_u8() == 1 {
        Ok(inv.unwrap())
      } else {
        Err(SynthesisError::DivisionByZero)
      }
    })?;

    cs.enforce(
      || "Check denumy inverse",
      |lc| lc + denumy.get_variable(),
      |lc| lc + denumy_inv.get_variable(),
      |lc| lc + CS::one(),
    );

    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
      Ok(*xxyy.get_value().get()? * *denumy_inv.get_value().get()?)
    })?;

    cs.enforce(
      || "Check that y is correct",
      |lc| lc + xxyy.get_variable(),
      |lc| lc + denumy_inv.get_variable(),
      |lc| lc + y.get_variable(),
    );

    let is_infinity = AllocatedNum::alloc(cs.namespace(|| "is infinity"), || Ok(Fp::zero()))?;

    Ok(Self { x, y, is_infinity })
  }

  /// A gadget for scalar multiplication.
  pub fn scalar_mul<CS: ConstraintSystem<Fp>>(
    &self,
    mut cs: CS,
    scalar: Vec<AllocatedBit>,
  ) -> Result<Self, SynthesisError> {
    let mut res = Self::default(cs.namespace(|| "res"))?;
    for i in (0..249).rev() {
      //dbg!(scalar[i].get_value().unwrap());
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
use zerocaf::constants::{EDWARDS_A, EDWARDS_D};

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
    Self { x, y, is_infinity }
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

    let xv = self.X * other.Y;
    let yu = self.Y * other.X;
    let pResX = xv + yu;

    let xu = self.X * other.X;
    let yv = self.Y * other.Y;
    let pResY = yv + xu;

    let dxyuv = xv * yu * constants::EDWARDS_D;
    let one = FieldElement::one();
    let denx = one + dxyuv;
    let deny = one - dxyuv;
    Self {
      x: pResX / denx,
      y: pResY / deny,
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

    let xx = self.X * self.X;
    let yy = self.Y * self.Y;
    let xy = self.X * self.Y;
    let denumx = yy - xx;

    let one = FieldElement::one();
    let two = one + one;
    let denumy = -denumx + two;
    Self {
      x: (xy + xy) / denumx,
      y: (xx + yy) / denumy,
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
