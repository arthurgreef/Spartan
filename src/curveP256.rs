#![allow(missing_docs)]

use crate::traits::{ChallengeTrait, CompressedGroup, Group};
use core::ops::Mul;
use data_encoding::HEXLOWER;
use ff::{
  derive::bitvec::{array::BitArray, order::Lsb0},
  Field, FieldBits, PrimeField, PrimeFieldBits,
};
use merlin::Transcript;
use p256::{
  elliptic_curve::{
    group::GroupEncoding, hash2field::ExpandMsgXmd, hash2curve::GroupDigest, Curve, bigint::Encoding,
  },
  ProjectivePoint, Scalar, CompressedPoint, NistP256,
};
use rug::Integer;
use sha2::Sha256;
use std::ops::{Add, AddAssign, MulAssign, Neg, Sub, SubAssign};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
pub struct P256Scalar(pub Scalar);

impl From<u64> for P256Scalar {
  fn from(d: u64) -> P256Scalar {
    Self(Scalar::from(d))
  }
}

impl ConstantTimeEq for P256Scalar {
  fn ct_eq(&self, other: &Self) -> subtle::Choice {
    self.0.ct_eq(&other.0)
  }
}

impl ConditionallySelectable for P256Scalar {
  fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
    Self(Scalar::conditional_select(&a.0, &b.0, choice))
  }
}

impl Field for P256Scalar {
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
    CtOption::new(Self(self.0.invert().unwrap()), Choice::from(1u8))
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
impl<'a, 'b> Add<&'b P256Scalar> for &'a P256Scalar {
  type Output = P256Scalar;

  #[inline]
  fn add(self, rhs: &'b P256Scalar) -> Self::Output {
    *self + *rhs
  }
}

impl<'b> Add<&'b P256Scalar> for P256Scalar {
  type Output = Self;

  #[inline]
  fn add(self, rhs: &'b P256Scalar) -> Self::Output {
    self + *rhs
  }
}

impl<'a> Add<P256Scalar> for &'a P256Scalar {
  type Output = P256Scalar;

  #[inline]
  fn add(self, rhs: P256Scalar) -> Self::Output {
    *self + rhs
  }
}

impl Add for P256Scalar {
  type Output = Self;

  #[inline]
  fn add(self, rhs: P256Scalar) -> Self::Output {
    P256Scalar(self.0 + rhs.0)
  }
}

impl AddAssign for P256Scalar {
  #[inline]
  fn add_assign(&mut self, rhs: Self) {
    *self = *self + rhs;
  }
}

impl<'b> AddAssign<&'b P256Scalar> for P256Scalar {
  #[inline]
  fn add_assign(&mut self, rhs: &'b P256Scalar) {
    *self = *self + rhs;
  }
}

impl<'a, 'b> Sub<&'b P256Scalar> for &'a P256Scalar {
  type Output = P256Scalar;

  #[inline]
  fn sub(self, rhs: &'b P256Scalar) -> Self::Output {
    *self - *rhs
  }
}

impl<'b> Sub<&'b P256Scalar> for P256Scalar {
  type Output = Self;

  #[inline]
  fn sub(self, rhs: &'b P256Scalar) -> Self::Output {
    self - *rhs
  }
}

impl<'a> Sub<P256Scalar> for &'a P256Scalar {
  type Output = P256Scalar;

  #[inline]
  fn sub(self, rhs: P256Scalar) -> Self::Output {
    *self - rhs
  }
}

impl Sub for P256Scalar {
  type Output = Self;

  #[inline]
  fn sub(self, rhs: P256Scalar) -> Self::Output {
    P256Scalar(self.0 - rhs.0)
  }
}

impl SubAssign for P256Scalar {
  #[inline]
  fn sub_assign(&mut self, rhs: Self) {
    *self = *self - rhs;
  }
}

impl<'b> SubAssign<&'b P256Scalar> for P256Scalar {
  #[inline]
  fn sub_assign(&mut self, rhs: &'b P256Scalar) {
    *self = *self - rhs;
  }
}

impl<'a, 'b> Mul<&'b P256Scalar> for &'a P256Scalar {
  type Output = P256Scalar;

  #[inline]
  fn mul(self, rhs: &'b P256Scalar) -> Self::Output {
    *self * *rhs
  }
}

impl<'b> Mul<&'b P256Scalar> for P256Scalar {
  type Output = Self;

  #[inline]
  fn mul(self, rhs: &'b P256Scalar) -> Self::Output {
    self * *rhs
  }
}

impl<'a> Mul<P256Scalar> for &'a P256Scalar {
  type Output = P256Scalar;

  #[inline]
  fn mul(self, rhs: P256Scalar) -> Self::Output {
    *self * rhs
  }
}

impl Mul for P256Scalar {
  type Output = Self;

  #[inline]
  fn mul(self, rhs: P256Scalar) -> Self::Output {
    P256Scalar(self.0 * rhs.0)
  }
}

impl MulAssign for P256Scalar {
  #[inline]
  fn mul_assign(&mut self, rhs: Self) {
    *self = *self * rhs;
  }
}

impl<'b> MulAssign<&'b P256Scalar> for P256Scalar {
  #[inline]
  fn mul_assign(&mut self, rhs: &'b P256Scalar) {
    *self = *self * rhs;
  }
}

impl<'a> Neg for &'a P256Scalar {
  type Output = P256Scalar;

  #[inline]
  fn neg(self) -> Self::Output {
    P256Scalar(self.0.neg())
  }
}

impl Neg for P256Scalar {
  type Output = Self;

  #[inline]
  fn neg(self) -> Self::Output {
    -&self
  }
}

impl PrimeField for P256Scalar {
  type Repr = [u8; 32];

  const NUM_BITS: u32 = 256;
  const CAPACITY: u32 = 255;
  const S: u32 = 4;

  fn from_repr(bytes: Self::Repr) -> CtOption<Self> {
    let gbytes = generic_array::GenericArray::from(bytes);
    CtOption::new(
      P256Scalar(Scalar::from_repr(gbytes).unwrap()),
      Choice::from(1u8),
    )
  }

  fn to_repr(&self) -> [u8; 32] {
    let mut bytes = [0u8;32];
    bytes.copy_from_slice(&self.0.to_repr()[0..32]);
    bytes
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

impl PrimeFieldBits for P256Scalar {
  type ReprBits = [u8; 32];

  fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(&self.0.to_repr()[0..32]);
    BitArray::<Lsb0, _>::new(bytes)
  }

  fn char_le_bits() -> FieldBits<Self::ReprBits> {
    unimplemented!();
  }
}

impl Mul<P256Scalar> for ProjectivePoint {
  type Output = ProjectivePoint;

  fn mul(self, _other: P256Scalar) -> ProjectivePoint {
    unimplemented!();
  }
}

impl Mul<&P256Scalar> for ProjectivePoint {
  type Output = ProjectivePoint;

  fn mul(self, _other: &P256Scalar) -> ProjectivePoint {
    unimplemented!();
  }
}

impl MulAssign<P256Scalar> for ProjectivePoint {
  fn mul_assign(&mut self, _rhs: P256Scalar) {
    unimplemented!();
  }
}

impl MulAssign<&P256Scalar> for ProjectivePoint {
  fn mul_assign(&mut self, _rhs: &P256Scalar) {
    unimplemented!();
  }
}

impl Group for ProjectivePoint {
  type Base = P256Scalar;
  type Scalar = P256Scalar;
  type CompressedGroupElement = CompressedPoint;
  type PreprocessedGroupElement = ProjectivePoint;

  fn vartime_multiscalar_mul(
    scalars: &[Self::Scalar],
    bases: &[Self::PreprocessedGroupElement],
  ) -> Self {
    // Unoptimized.
    scalars
      .iter()
      .zip(bases)
      .map(|(scalar, base)| base.mul(&scalar.0))
      .fold(ProjectivePoint::IDENTITY, |acc, x| acc + x)
  }

  fn compress(&self) -> Self::CompressedGroupElement {
    self.to_bytes()
  }

  fn from_uniform_bytes(bytes: &[u8]) -> Option<Self::PreprocessedGroupElement> {
    if bytes.len() != 64 {
      None
    } else {
      Some(NistP256::hash_from_bytes::<ExpandMsgXmd<Sha256>>(&[bytes], b"Spartan-P256-Snark").unwrap())
    }
  }

  fn to_coordinates(&self) -> (Self::Base, Self::Base, bool) {
    unimplemented!();
  }

  fn get_order() -> Integer {
    let order = Integer::from_str_radix(&HEXLOWER.encode(&NistP256::ORDER.to_le_bytes()), 16).unwrap();
    println!("order: {}", &order);
    order
  }
}

impl ChallengeTrait for P256Scalar {
  fn challenge(label: &'static [u8], transcript: &mut Transcript) -> Self {
    // rand compatibiliity problems
    //   let mut key: <ChaCha20Rng as SeedableRng>::Seed = Default::default();
    //   transcript.challenge_bytes(label, &mut key);
    //   let mut rng = ChaCha20Rng::from_seed(key);
    //P256Scalar(Scalar::random(&mut rand_core_latest::OsRng))
    unimplemented!();
  }
}

impl CompressedGroup for CompressedPoint {
  type GroupElement = ProjectivePoint;

  fn decompress(&self) -> Option<Self::GroupElement> {
    Some(ProjectivePoint::from_bytes(self).unwrap())
  }
  fn as_bytes(&self) -> &[u8] {
    unimplemented!();
  }
}
