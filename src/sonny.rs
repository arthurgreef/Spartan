#![allow(missing_docs)]

extern crate zerocaf;

use crate::traits::{ChallengeTrait, CompressedGroup, Group};
use core::ops::Mul;
use data_encoding::HEXLOWER;
use merlin::Transcript;
use num_bigint::BigInt;
use num_traits::Num;
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use zerocaf::{
  backend::u64::{constants, field::FieldElement},
  edwards::{AffinePoint, CompressedEdwardsY, EdwardsPoint},
  ristretto::RistrettoPoint,
  scalar::Scalar,
};

impl Group for EdwardsPoint {
  type Base = FieldElement;
  type Scalar = Scalar;
  type CompressedGroupElement = CompressedEdwardsY;
  type PreprocessedGroupElement = AffinePoint;

  fn vartime_multiscalar_mul(
    scalars: &[Self::Scalar],
    bases: &[Self::PreprocessedGroupElement],
  ) -> Self {
    unimplemented!()
  }

  fn compress(&self) -> Self::CompressedGroupElement {
    self.compress()
  }

  fn from_uniform_bytes(bytes: &[u8]) -> Option<Self::PreprocessedGroupElement> {
    if bytes.len() != 64 {
      None
    } else {
      let mut ubytes = [0u8; 64];
      ubytes.copy_from_slice(bytes);
      let edwards_point = RistrettoPoint::from_uniform_bytes(&ubytes).0;
      Some(AffinePoint::from(edwards_point))
    }
  }

  fn to_coordinates(&self) -> (Self::Base, Self::Base, bool) {
    let point = AffinePoint::from(*self);
    (point.X, point.Y, false)
  }

  fn get_order() -> BigInt {
    BigInt::from_str_radix(&HEXLOWER.encode(&constants::L.to_bytes()[..]), 16).unwrap()
  }
}

impl ChallengeTrait for Scalar {
  fn challenge(label: &'static [u8], transcript: &mut Transcript) -> Self {
    let mut key: <ChaCha20Rng as SeedableRng>::Seed = Default::default();
    transcript.challenge_bytes(label, &mut key);
    let mut rng = ChaCha20Rng::from_seed(key);
    Scalar::random(&mut rng)
  }
}

impl CompressedGroup for CompressedEdwardsY {
  type GroupElement = EdwardsPoint;

  fn decompress(&self) -> Option<EdwardsPoint> {
    self.decompress()
  }

  fn as_bytes(&self) -> &[u8] {
    self.as_bytes()
  }
}
