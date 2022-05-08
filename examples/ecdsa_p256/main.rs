use std::ops::{Add, AddAssign, Mul, MulAssign, Neg};

use ff::PrimeField;
use p256::{
  self,
  elliptic_curve::{
    hash2field::{hash_to_field, ExpandMsgXmd},
    ScalarCore,
  },
  NistP256, NonZeroScalar, ProjectivePoint,
};
use rand_latest::RngCore;
use rand_core_latest::OsRng;
use sha2::Sha256;

type P = p256::ProjectivePoint;
type S = p256::Scalar;

#[derive(Debug, Clone, Copy)]
pub struct SecretKey(pub S);

impl SecretKey {
  pub fn random() -> Self {
    let secret = S::from_repr(NonZeroScalar::random(&mut OsRng).into()).unwrap();
    Self(secret)
  }
}

#[derive(Debug, Clone, Copy)]
pub struct PublicKey(pub P);

impl PublicKey {
  pub fn from_secret_key(s: &SecretKey) -> Self {
    let point = ProjectivePoint::GENERATOR * s.0;
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
    let messages = &[&t[..], &c.to_repr()[..]];
    let dst: &[u8] = b"SPARTAN_ECDSA_P256";
    let mut u = [S::default()];
    hash_to_field::<ExpandMsgXmd<Sha256>, S>(messages, dst, &mut u).unwrap();
    let r = u[0];

    // [r]G
    let r_g = ProjectivePoint::GENERATOR * r;

    // s = r + c . sk
    let mut s = c;

    s.mul_assign(&self.0);
    s.add_assign(&r);

    Signature { r: r_g, s }
  }
}

impl PublicKey {
  pub fn verify_commitment(&self, c: S, signature: &Signature) -> bool {
    let modulus: S = S::from_str_vartime(&ScalarCore::<NistP256>::MODULUS.to_string()).unwrap();
    let order_check_pk = self.0.mul(modulus);
    if !order_check_pk.eq(&ProjectivePoint::IDENTITY) {
      return false;
    }

    let order_check_r = signature.r.mul(modulus);
    if !order_check_r.eq(&ProjectivePoint::IDENTITY) {
      return false;
    }

    // 0 = -S . P_G + R + c . pk
    self
      .0
      .mul(c)
      .add(&signature.r)
      .add(ProjectivePoint::GENERATOR.mul(signature.s).neg())
      .eq(&ProjectivePoint::IDENTITY)
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

  let dst: &[u8] = b"SPARTAN_ECDSA_P256";
    let mut u = [S::default()];
    hash_to_field::<ExpandMsgXmd<Sha256>, S>(&[digest.as_ref()], dst, &mut u).unwrap();
    let c = u[0];


  let signature = sk.sign_commitment(c, &mut OsRng);
  assert!(pk.verify_commitment(c, &signature));
}
