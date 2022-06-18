#![allow(missing_docs)]

extern crate zerocaf;

use core::ops::Mul;
use curve25519_dalek::{
  edwards::{CompressedEdwardsY, EdwardsPoint},
  scalar::Scalar,
  traits::Identity,
};
use ff::{Field, FieldBits, PrimeField, PrimeFieldBits};
use merlin::Transcript;
use num_bigint::BigInt;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use std::ops::{Add, AddAssign, MulAssign, Neg, Sub, SubAssign};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use zerocaf::{field::FieldElement};

//use crate::scalar::ristretto255::Scalar;

use crate::traits::{ChallengeTrait, CompressedGroup, Group};

type FieldBytes = [u8; 32];

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
pub struct DScalar(pub Scalar);

impl From<u64> for DScalar {
  fn from(d: u64) -> DScalar {
    Self(Scalar::from(d))
  }
}

impl ConstantTimeEq for DScalar {
  fn ct_eq(&self, other: &Self) -> subtle::Choice {
    self.0.ct_eq(&other.0)
  }
}

impl ConditionallySelectable for DScalar {
  fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
    Self(Scalar::conditional_select(&a.0, &b.0, choice))
  }
}

impl Field for DScalar {
  fn random(_: impl rand_core_latest::RngCore) -> Self {
    // Incompatible RngCore versions
    unimplemented!()
  }

  fn zero() -> Self {
    Self(Scalar::zero())
  }

  fn one() -> Self {
    Self(Scalar::one())
  }

  fn is_zero(&self) -> subtle::Choice {
    self.0.ct_eq(&Scalar::zero())
  }

  fn square(&self) -> Self {
    Self(self.0 * self.0)
  }

  fn double(&self) -> Self {
    Self(self.0 + self.0)
  }

  fn invert(&self) -> CtOption<Self> {
    CtOption::new(Self(self.0.invert()), Choice::from(1u8))
  }

  fn sqrt(&self) -> CtOption<Self> {
    unimplemented!()
  }

  fn is_zero_vartime(&self) -> bool {
    self.is_zero().into()
  }

  fn cube(&self) -> Self {
    self.square() * self
  }

  fn pow_vartime<S: AsRef<[u64]>>(&self, exp: S) -> Self {
    let mut res = Self::one();
    for e in exp.as_ref().iter().rev() {
      for i in (0..64).rev() {
        res = res.square();

        if ((*e >> i) & 1) == 1 {
          res.mul_assign(self);
        }
      }
    }

    res
  }
}

impl<'a, 'b> Add<&'b DScalar> for &'a DScalar {
  type Output = DScalar;

  #[inline]
  fn add(self, rhs: &'b DScalar) -> Self::Output {
    *self + *rhs
  }
}

impl<'b> Add<&'b DScalar> for DScalar {
  type Output = Self;

  #[inline]
  fn add(self, rhs: &'b DScalar) -> Self::Output {
    self + *rhs
  }
}

impl<'a> Add<DScalar> for &'a DScalar {
  type Output = DScalar;

  #[inline]
  fn add(self, rhs: DScalar) -> Self::Output {
    *self + rhs
  }
}

impl Add for DScalar {
  type Output = Self;

  #[inline]
  fn add(self, rhs: DScalar) -> Self::Output {
    DScalar(self.0 + rhs.0)
  }
}

impl AddAssign for DScalar {
  #[inline]
  fn add_assign(&mut self, rhs: Self) {
    *self = *self + rhs;
  }
}

impl<'b> AddAssign<&'b DScalar> for DScalar {
  #[inline]
  fn add_assign(&mut self, rhs: &'b DScalar) {
    *self = *self + rhs;
  }
}

impl<'a, 'b> Sub<&'b DScalar> for &'a DScalar {
  type Output = DScalar;

  #[inline]
  fn sub(self, rhs: &'b DScalar) -> Self::Output {
    *self - *rhs
  }
}

impl<'b> Sub<&'b DScalar> for DScalar {
  type Output = Self;

  #[inline]
  fn sub(self, rhs: &'b DScalar) -> Self::Output {
    self - *rhs
  }
}

impl<'a> Sub<DScalar> for &'a DScalar {
  type Output = DScalar;

  #[inline]
  fn sub(self, rhs: DScalar) -> Self::Output {
    *self - rhs
  }
}

impl Sub for DScalar {
  type Output = Self;

  #[inline]
  fn sub(self, rhs: DScalar) -> Self::Output {
    DScalar(self.0 - rhs.0)
  }
}

impl SubAssign for DScalar {
  #[inline]
  fn sub_assign(&mut self, rhs: Self) {
    *self = *self - rhs;
  }
}

impl<'b> SubAssign<&'b DScalar> for DScalar {
  #[inline]
  fn sub_assign(&mut self, rhs: &'b DScalar) {
    *self = *self - rhs;
  }
}

impl<'a, 'b> Mul<&'b DScalar> for &'a DScalar {
  type Output = DScalar;

  #[inline]
  fn mul(self, rhs: &'b DScalar) -> Self::Output {
    *self * *rhs
  }
}

impl<'b> Mul<&'b DScalar> for DScalar {
  type Output = Self;

  #[inline]
  fn mul(self, rhs: &'b DScalar) -> Self::Output {
    self * *rhs
  }
}

impl<'a> Mul<DScalar> for &'a DScalar {
  type Output = DScalar;

  #[inline]
  fn mul(self, rhs: DScalar) -> Self::Output {
    *self * rhs
  }
}

impl Mul for DScalar {
  type Output = Self;

  #[inline]
  fn mul(self, rhs: DScalar) -> Self::Output {
    DScalar(self.0 * rhs.0)
  }
}

impl MulAssign for DScalar {
  #[inline]
  fn mul_assign(&mut self, rhs: Self) {
    *self = *self * rhs;
  }
}

impl<'b> MulAssign<&'b DScalar> for DScalar {
  #[inline]
  fn mul_assign(&mut self, rhs: &'b DScalar) {
    *self = *self * rhs;
  }
}

impl<'a> Neg for &'a DScalar {
  type Output = DScalar;

  #[inline]
  fn neg(self) -> Self::Output {
    DScalar(self.0.neg())
  }
}

impl Neg for DScalar {
  type Output = Self;

  #[inline]
  fn neg(self) -> Self::Output {
    -&self
  }
}

impl PrimeField for DScalar {
  type Repr = FieldBytes;

  const NUM_BITS: u32 = 256;
  const CAPACITY: u32 = 255;
  const S: u32 = 4;

  fn from_repr(bytes: FieldBytes) -> CtOption<Self> {
    CtOption::new(
      DScalar(Scalar::from_bytes_mod_order(bytes)),
      Choice::from(1u8),
    )
  }

  fn to_repr(&self) -> FieldBytes {
    self.0.to_bytes()
  }

  fn is_odd(&self) -> Choice {
    unimplemented!();
  }

  fn multiplicative_generator() -> Self {
    unimplemented!();
  }

  fn root_of_unity() -> Self {
    unimplemented!();
  }
}

impl PrimeFieldBits for DScalar {
  type ReprBits = [u8; 32];

  fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
    self.0.to_bytes().into()
  }

  fn char_le_bits() -> FieldBits<Self::ReprBits> {
    unimplemented!();
  }
}

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
pub struct DEdwardsPoint(pub EdwardsPoint);

impl From<DEdwardsPoint> for EdwardsPoint {
  fn from(point: DEdwardsPoint) -> EdwardsPoint {
    point.0
  }
}

impl<'a> From<&'a DEdwardsPoint> for &'a EdwardsPoint {
  fn from(point: &'a DEdwardsPoint) -> &'a EdwardsPoint {
    &point.0
  }
}

impl Add<DEdwardsPoint> for DEdwardsPoint {
  type Output = DEdwardsPoint;
  fn add(self, other: DEdwardsPoint) -> DEdwardsPoint {
    DEdwardsPoint(self.0 + other.0)
  }
}

impl<'r> Add<&'r DEdwardsPoint> for DEdwardsPoint {
  type Output = DEdwardsPoint;
  fn add(self, other: &'r DEdwardsPoint) -> DEdwardsPoint {
    DEdwardsPoint(self.0 + other.0)
  }
}

impl AddAssign for DEdwardsPoint {
  #[inline]
  fn add_assign(&mut self, rhs: Self) {
    *self = *self + rhs;
  }
}

impl<'b> AddAssign<&'b DEdwardsPoint> for DEdwardsPoint {
  #[inline]
  fn add_assign(&mut self, rhs: &'b DEdwardsPoint) {
    *self = *self + rhs;
  }
}

impl Sub<DEdwardsPoint> for DEdwardsPoint {
  type Output = DEdwardsPoint;
  fn sub(self, other: DEdwardsPoint) -> DEdwardsPoint {
    &self - other
  }
}

impl<'b> Sub<&'b DEdwardsPoint> for DEdwardsPoint {
  type Output = Self;

  #[inline]
  fn sub(self, rhs: &'b DEdwardsPoint) -> Self::Output {
    DEdwardsPoint(self.0 - rhs.0)
  }
}

impl<'a> Sub<DEdwardsPoint> for &'a DEdwardsPoint {
  type Output = DEdwardsPoint;

  #[inline]
  fn sub(self, rhs: DEdwardsPoint) -> Self::Output {
    DEdwardsPoint(self.0 - rhs.0)
  }
}

impl SubAssign for DEdwardsPoint {
  #[inline]
  fn sub_assign(&mut self, rhs: Self) {
    *self = *self - rhs;
  }
}

impl<'b> SubAssign<&'b DEdwardsPoint> for DEdwardsPoint {
  #[inline]
  fn sub_assign(&mut self, rhs: &'b DEdwardsPoint) {
    *self = *self - rhs;
  }
}

impl<'b> Mul<&'b DScalar> for DEdwardsPoint {
  type Output = Self;

  #[inline]
  fn mul(self, rhs: &'b DScalar) -> Self::Output {
    DEdwardsPoint(self.0 * rhs.0)
  }
}

impl Mul<DScalar> for DEdwardsPoint {
  type Output = DEdwardsPoint;

  #[inline]
  fn mul(self, rhs: DScalar) -> Self::Output {
    DEdwardsPoint(self.0 * rhs.0)
  }
}

impl MulAssign<DScalar> for DEdwardsPoint {
  #[inline]
  fn mul_assign(&mut self, rhs: DScalar) {
    *self = *self * rhs;
  }
}

impl<'b> MulAssign<&'b DScalar> for DEdwardsPoint {
  #[inline]
  fn mul_assign(&mut self, rhs: &'b DScalar) {
    *self = *self * rhs;
  }
}

impl Group for DEdwardsPoint {
  type Base = FieldElement;  // TODO create one of these
  type Scalar = DScalar;
  type CompressedGroupElement = CompressedEdwardsY;
  type PreprocessedGroupElement = EdwardsPoint;

  fn vartime_multiscalar_mul(
    scalars: &[Self::Scalar],
    bases: &[Self::PreprocessedGroupElement],
  ) -> Self {
    scalars
      .iter()
      .zip(bases)
      .map(|(scalar, base)| DEdwardsPoint(base.mul(scalar.0)))
      .fold(DEdwardsPoint(EdwardsPoint::identity()), |acc, x| acc + x)
  }

  fn compress(&self) -> Self::CompressedGroupElement {
    self.0.compress()
  }

  fn from_uniform_bytes(bytes: &[u8]) -> Option<Self::PreprocessedGroupElement> {
    if bytes.len() != 64 {
      None
    } else {
      Some(EdwardsPoint::hash_from_bytes::<sha2::Sha512>(
        bytes,
      ))
    }
  }

  fn to_coordinates(&self) -> (Self::Base, Self::Base, bool) {
    unimplemented!();
  }

  fn get_order() -> BigInt {
    //BigInt::from_str_radix(&HEXLOWER.encode(&constants::L.to_bytes()[..]), 16).unwrap()
    unimplemented!();
  }
}

impl ChallengeTrait for DScalar {
  fn challenge(label: &'static [u8], transcript: &mut Transcript) -> Self {
    let mut key: <ChaCha20Rng as SeedableRng>::Seed = Default::default();
    transcript.challenge_bytes(label, &mut key);
    let mut rng = ChaCha20Rng::from_seed(key);
    DScalar(Scalar::random(&mut rng))
  }
}

impl CompressedGroup for CompressedEdwardsY {
  type GroupElement = DEdwardsPoint;

  fn decompress(&self) -> Option<DEdwardsPoint> {
    Some(DEdwardsPoint(self.decompress().unwrap()))
  }

  fn as_bytes(&self) -> &[u8] {
    self.as_bytes()
  }
}
