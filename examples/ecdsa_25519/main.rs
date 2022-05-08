use std::ops::{Add, AddAssign, Mul, MulAssign, Neg};

use curve25519_dalek::{
  constants::{BASEPOINT_ORDER, ED25519_BASEPOINT_POINT},
  edwards::EdwardsPoint,
  traits::Identity,
};
use rand::RngCore;
use rand_core::OsRng;
use sha2::Sha512;

type P = curve25519_dalek::edwards::EdwardsPoint;
type S = curve25519_dalek::scalar::Scalar;

#[derive(Debug, Clone, Copy)]
pub struct SecretKey(pub S);

impl SecretKey {
  pub fn random() -> Self {
    let secret = S::random(&mut OsRng);
    Self(secret)
  }
}

#[derive(Debug, Clone, Copy)]
pub struct PublicKey(pub P);

impl PublicKey {
  pub fn from_secret_key(s: &SecretKey) -> Self {
    let point = ED25519_BASEPOINT_POINT * s.0;
    Self(point)
  }
}

#[derive(Clone)]
pub struct Signature {
  pub r: P,
  pub s: S,
}

impl SecretKey {
  pub fn sign_commitment(self, c: S, mut rng: impl RngCore) -> Signature {
    // T
    let mut t = [0u8; 80];
    rng.fill_bytes(&mut t[..]);

    // r = H*(T || M)
    let r = S::hash_from_bytes::<Sha512>(&[&t[..], &c.to_bytes()].concat());

    // [r]G
    let r_g = ED25519_BASEPOINT_POINT * r;

    // s = r + c . sk
    let mut s = c;

    s.mul_assign(&self.0);
    s.add_assign(&r);

    Signature { r: r_g, s }
  }
}

impl PublicKey {
  pub fn verify_commitment(&self, c: S, signature: &Signature) -> bool {
    let modulus: S = BASEPOINT_ORDER;
    let order_check_pk = self.0.mul(modulus);
    if !order_check_pk.eq(&EdwardsPoint::identity()) {
      return false;
    }

    let order_check_r = signature.r.mul(modulus);
    if !order_check_r.eq(&EdwardsPoint::identity()) {
      return false;
    }

    // 0 = -S . P_G + R + c . pk
    self
      .0
      .mul(c)
      .add(&signature.r)
      .add(ED25519_BASEPOINT_POINT.mul(signature.s).neg())
      .eq(&EdwardsPoint::identity())
  }
}

fn main() {
  let sk = SecretKey::random();
  let pk = PublicKey::from_secret_key(&sk);

  let message = b"MESSAGE_16_BYTES";

  let mut digest: Vec<u8> = message.to_vec();
  for _ in 0..(32 - message.len() as u32) {
    digest.extend(&[0u8; 1]);
  }

  let c = S::hash_from_bytes::<Sha512>(digest.as_ref());

  let signature = sk.sign_commitment(c, &mut OsRng);
  assert!(pk.verify_commitment(c, &signature));
}
