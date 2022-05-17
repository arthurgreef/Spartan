use std::ops::{Add, AddAssign, Mul, MulAssign, Neg};

use data_encoding::HEXLOWER;
use ff::PrimeField;
use p256::{
  self,
  elliptic_curve::{
    hash2field::{hash_to_field, ExpandMsgXmd},
    ScalarCore,
  },
  NistP256, NonZeroScalar, ProjectivePoint, Scalar,
};
use rand_core_latest::OsRng;
use rand_latest::RngCore;
use rug::Integer;
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

fn int(bytes: &[u8]) -> Integer {
  Integer::from_str_radix(&HEXLOWER.encode(&bytes), 16).unwrap()
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

    let (rxf, ryf) = r_g.to_affine().coordinates();
    let (rx, ry) = (
      Scalar::from_repr(rxf.to_bytes()).unwrap(),
      Scalar::from_repr(ryf.to_bytes()).unwrap(),
    );

    println!("n.rx: {}", int(&rxf.to_bytes()));
    println!("n.ry: {}", int(&ryf.to_bytes()));

    // s = r + c . sk
    let mut s = c;

    s.mul_assign(&self.0);
    s.add_assign(&r);

    println!("n.s: {}", int(&s.to_bytes()));

    Signature { r: r_g, s }
  }
}

impl PublicKey {
  pub fn verify_commitment(&self, c: S, signature: &Signature) -> bool {
    let modulus_str =
      rug::Integer::from_str_radix(&ScalarCore::<NistP256>::MODULUS.to_string(), 16).unwrap();
    let modulus: S = S::from_str_vartime(&modulus_str.to_string_radix(10)).unwrap();
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
