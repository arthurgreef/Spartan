#![allow(missing_docs)]

use crate::traits::{ChallengeTrait, CompressedGroup, Group};
use core::ops::Mul;
use curve25519_dalek::{
  constants::BASEPOINT_ORDER,
  edwards::{self, CompressedEdwardsY},
  scalar::{self},
  traits::Identity,
};
use data_encoding::HEXLOWER;
use ff::{
  derive::bitvec::{array::BitArray, order::Lsb0},
  Field, FieldBits, PrimeField, PrimeFieldBits,
};
use merlin::Transcript;
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use rug::Integer;
use sha2::Sha256;
use std::ops::{Add, AddAssign, MulAssign, Neg, Sub, SubAssign};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

type FieldBytes = [u8; 32];

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
pub struct C25519Scalar(pub scalar::Scalar);

impl From<u64> for C25519Scalar {
  fn from(d: u64) -> C25519Scalar {
    Self(scalar::Scalar::from(d))
  }
}

impl ConstantTimeEq for C25519Scalar {
  fn ct_eq(&self, other: &Self) -> subtle::Choice {
    self.0.ct_eq(&other.0)
  }
}

impl ConditionallySelectable for C25519Scalar {
  fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
    Self(scalar::Scalar::conditional_select(&a.0, &b.0, choice))
  }
}

impl Field for C25519Scalar {
  fn random(_: impl rand_core_latest::RngCore) -> Self {
    // Incompatible RngCore versions
    unimplemented!()
  }

  fn zero() -> Self {
    Self(scalar::Scalar::zero())
  }

  fn one() -> Self {
    Self(scalar::Scalar::one())
  }

  fn is_zero(&self) -> subtle::Choice {
    self.0.ct_eq(&scalar::Scalar::zero())
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
    // Not used for secret sharing
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
impl<'a, 'b> Add<&'b C25519Scalar> for &'a C25519Scalar {
  type Output = C25519Scalar;

  #[inline]
  fn add(self, rhs: &'b C25519Scalar) -> Self::Output {
    *self + *rhs
  }
}

impl<'b> Add<&'b C25519Scalar> for C25519Scalar {
  type Output = Self;

  #[inline]
  fn add(self, rhs: &'b C25519Scalar) -> Self::Output {
    self + *rhs
  }
}

impl<'a> Add<C25519Scalar> for &'a C25519Scalar {
  type Output = C25519Scalar;

  #[inline]
  fn add(self, rhs: C25519Scalar) -> Self::Output {
    *self + rhs
  }
}

impl Add for C25519Scalar {
  type Output = Self;

  #[inline]
  fn add(self, rhs: C25519Scalar) -> Self::Output {
    C25519Scalar(self.0 + rhs.0)
  }
}

impl AddAssign for C25519Scalar {
  #[inline]
  fn add_assign(&mut self, rhs: Self) {
    *self = *self + rhs;
  }
}

impl<'b> AddAssign<&'b C25519Scalar> for C25519Scalar {
  #[inline]
  fn add_assign(&mut self, rhs: &'b C25519Scalar) {
    *self = *self + rhs;
  }
}

impl<'a, 'b> Sub<&'b C25519Scalar> for &'a C25519Scalar {
  type Output = C25519Scalar;

  #[inline]
  fn sub(self, rhs: &'b C25519Scalar) -> Self::Output {
    *self - *rhs
  }
}

impl<'b> Sub<&'b C25519Scalar> for C25519Scalar {
  type Output = Self;

  #[inline]
  fn sub(self, rhs: &'b C25519Scalar) -> Self::Output {
    self - *rhs
  }
}

impl<'a> Sub<C25519Scalar> for &'a C25519Scalar {
  type Output = C25519Scalar;

  #[inline]
  fn sub(self, rhs: C25519Scalar) -> Self::Output {
    *self - rhs
  }
}

impl Sub for C25519Scalar {
  type Output = Self;

  #[inline]
  fn sub(self, rhs: C25519Scalar) -> Self::Output {
    C25519Scalar(self.0 - rhs.0)
  }
}

impl SubAssign for C25519Scalar {
  #[inline]
  fn sub_assign(&mut self, rhs: Self) {
    *self = *self - rhs;
  }
}

impl<'b> SubAssign<&'b C25519Scalar> for C25519Scalar {
  #[inline]
  fn sub_assign(&mut self, rhs: &'b C25519Scalar) {
    *self = *self - rhs;
  }
}

impl<'a, 'b> Mul<&'b C25519Scalar> for &'a C25519Scalar {
  type Output = C25519Scalar;

  #[inline]
  fn mul(self, rhs: &'b C25519Scalar) -> Self::Output {
    *self * *rhs
  }
}

impl<'b> Mul<&'b C25519Scalar> for C25519Scalar {
  type Output = Self;

  #[inline]
  fn mul(self, rhs: &'b C25519Scalar) -> Self::Output {
    self * *rhs
  }
}

impl<'a> Mul<C25519Scalar> for &'a C25519Scalar {
  type Output = C25519Scalar;

  #[inline]
  fn mul(self, rhs: C25519Scalar) -> Self::Output {
    *self * rhs
  }
}

impl Mul for C25519Scalar {
  type Output = Self;

  #[inline]
  fn mul(self, rhs: C25519Scalar) -> Self::Output {
    C25519Scalar(self.0 * rhs.0)
  }
}

impl MulAssign for C25519Scalar {
  #[inline]
  fn mul_assign(&mut self, rhs: Self) {
    *self = *self * rhs;
  }
}

impl<'b> MulAssign<&'b C25519Scalar> for C25519Scalar {
  #[inline]
  fn mul_assign(&mut self, rhs: &'b C25519Scalar) {
    *self = *self * rhs;
  }
}

impl<'a> Neg for &'a C25519Scalar {
  type Output = C25519Scalar;

  #[inline]
  fn neg(self) -> Self::Output {
    C25519Scalar(self.0.neg())
  }
}

impl Neg for C25519Scalar {
  type Output = Self;

  #[inline]
  fn neg(self) -> Self::Output {
    -&self
  }
}

impl PrimeField for C25519Scalar {
  type Repr = FieldBytes;

  const NUM_BITS: u32 = 256;
  const CAPACITY: u32 = 255;
  const S: u32 = 4;

  fn from_repr(bytes: FieldBytes) -> CtOption<Self> {
    CtOption::new(
      C25519Scalar(scalar::Scalar::from_canonical_bytes(bytes).unwrap()),
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
    7u64.into()
  }

  fn root_of_unity() -> Self {
    unimplemented!();
  }
}

impl PrimeFieldBits for C25519Scalar {
  type ReprBits = [u8; 32];

  fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
    BitArray::<Lsb0, _>::new(*self.0.as_bytes())
  }

  fn char_le_bits() -> FieldBits<Self::ReprBits> {
    unimplemented!();
  }
}

impl Mul<C25519Scalar> for edwards::EdwardsPoint {
  type Output = edwards::EdwardsPoint;

  fn mul(self, _other: C25519Scalar) -> edwards::EdwardsPoint {
    unimplemented!();
  }
}

impl Mul<&C25519Scalar> for edwards::EdwardsPoint {
  type Output = edwards::EdwardsPoint;

  fn mul(self, _other: &C25519Scalar) -> edwards::EdwardsPoint {
    unimplemented!();
  }
}

impl MulAssign<C25519Scalar> for edwards::EdwardsPoint {
  fn mul_assign(&mut self, _rhs: C25519Scalar) {
    unimplemented!();
  }
}

impl MulAssign<&C25519Scalar> for edwards::EdwardsPoint {
  fn mul_assign(&mut self, _rhs: &C25519Scalar) {
    unimplemented!();
  }
}

impl Group for edwards::EdwardsPoint {
  type Base = C25519Scalar;
  type Scalar = C25519Scalar;
  type CompressedGroupElement = CompressedEdwardsY;
  type PreprocessedGroupElement = edwards::EdwardsPoint;

  fn vartime_multiscalar_mul(
    scalars: &[Self::Scalar],
    bases: &[Self::PreprocessedGroupElement],
  ) -> Self {
    // Unoptimized.
    scalars
      .iter()
      .zip(bases)
      .map(|(scalar, base)| base.mul(scalar.0))
      .fold(edwards::EdwardsPoint::identity(), |acc, x| acc + x)
  }

  fn compress(&self) -> Self::CompressedGroupElement {
    self.compress()
  }

  fn from_uniform_bytes(bytes: &[u8]) -> Option<Self::PreprocessedGroupElement> {
    if bytes.len() != 64 {
      None
    } else {
      Some(edwards::EdwardsPoint::hash_from_bytes::<sha2::Sha512>(
        bytes,
      ))
    }
  }

  fn to_coordinates(&self) -> (Self::Base, Self::Base, bool) {
    unimplemented!();
  }

  fn get_order() -> Integer {
    Integer::from_str_radix(&HEXLOWER.encode(&BASEPOINT_ORDER.to_bytes()[..]), 16).unwrap()
  }
}

impl ChallengeTrait for C25519Scalar {
  fn challenge(label: &'static [u8], transcript: &mut Transcript) -> Self {
    let mut key: <ChaCha20Rng as SeedableRng>::Seed = Default::default();
    transcript.challenge_bytes(label, &mut key);
    let mut rng = ChaCha20Rng::from_seed(key);
    C25519Scalar(scalar::Scalar::random(&mut rng))
  }
}

impl CompressedGroup for CompressedEdwardsY {
  type GroupElement = edwards::EdwardsPoint;

  fn decompress(&self) -> Option<edwards::EdwardsPoint> {
    self.decompress()
  }
  fn as_bytes(&self) -> &[u8] {
    self.as_bytes()
  }
}
