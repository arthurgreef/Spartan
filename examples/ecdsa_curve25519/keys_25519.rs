extern crate rand;
extern crate zerocaf;

use std::ops::{Add, Mul, Neg};

//use ff::PrimeFieldBits;
use rand::{thread_rng, Rng};
use sha2::Sha512;
use zerocaf::{
  backend::u64::constants,
  constants::BASEPOINT,
  //edwards::{double_and_add, ltr_bin_mul_edwards, AffinePoint, EdwardsPoint, ltr_bin_mul, binary_naf_mul, ProjectivePoint},
  //scalar::Scalar,
  traits::Identity,
};

//use curve25519_dalek;

use crate::{Fqs, Gs};

#[derive(Debug, Clone, Copy)]
pub struct SecretKey(pub Fqs);

impl SecretKey {
  pub fn random() -> Self {
    let mut bytes = [0u8; 32];
    thread_rng()
      .try_fill(&mut bytes[..31])
      .expect("Error getting the random bytes");
    let secret = Fqs::from_bytes(&bytes);
    Self(secret)
  }
}

#[derive(Debug, Clone, Copy)]
pub struct PublicKey(pub Gs);

impl PublicKey {
  pub fn from_secret_key(s: &SecretKey) -> Self {
    let point = BASEPOINT * s.0;
    Self(point)
  }
}

#[derive(Clone)]
pub struct Signature {
  pub r: Gs,
  pub s: Fqs,
}

impl SecretKey {
  pub fn sign_commitment(self, c: Fqs) -> Signature {
    // T
    let mut t = [0u8; 80];
    thread_rng()
      .try_fill(&mut t[..])
      .expect("Error getting the random bytes");

    // r = H*(T || M)
    let r = Fqs::hash_from_bytes::<Sha512>(&[&t[..], &c.to_bytes()].concat());

    // [r]G
    let r_g = BASEPOINT * r;

    // s = r + c . sk
    let mut s = c;

    s = s * self.0;
    s = s + r;

    //----------
    // let g_xy = AffinePoint::from(BASEPOINT);
    // println!("g.X.n: {:?}", Scalar::from(&g_xy.X));
    // println!("g.Y.n: {:?}", Scalar::from(&g_xy.Y));

    // println!("s.n: {:?}", s.to_le_bits());

    // println!("**************************************************");
    // let sg = BASEPOINT * s;
    // println!();
    // println!("oo:sg: {:?}", AffinePoint::from(sg));
    // println!("**************************************************");
    // let sg_xy = AffinePoint::from(sg);
    // let sg_xy = AffinePoint::from(sg);
    // println!("n.sgx: {:?}", curve25519_dalek::scalar::Scalar::from(&sg_xy.X).to_bytes());
    // println!("n.sgy: {:?}", curve25519_dalek::scalar::Scalar::from(&sg_xy.Y).to_bytes());

    // let sg1 = double_and_add(&BASEPOINT, &s);
    // let sg1_xy = AffinePoint::from(sg1);
    // println!("sg1.X.n: {:?}", Scalar::from(&sg1_xy.X));
    // println!("sg1.Y.n: {:?}", Scalar::from(&sg1_xy.Y));

    // let sg11 = ltr_bin_mul(&BASEPOINT, &s);
    // let sg11_xy = AffinePoint::from(sg11);
    // println!("sg11.X.n: {:?}", Scalar::from(&sg11_xy.X));
    // println!("sg11.Y.n: {:?}", Scalar::from(&sg11_xy.Y));
    // println!("..................................................");
    // let sg = ltr_bin_mul_edwards(&BASEPOINT, &s);
    // println!();
    // println!("off:sg: {:?}", AffinePoint::from(sg));
    // println!("..................................................");
    // let sg_xy = AffinePoint::from(sg);
    // println!("n.sgx: {:?}", curve25519_dalek::scalar::Scalar::from(&sg_xy.X));
    // println!("n.sgy: {:?}", curve25519_dalek::scalar::Scalar::from(&sg_xy.Y));
    //----------

    Signature { r: r_g, s }
  }
}

impl PublicKey {
  pub fn verify_commitment(&self, c: Fqs, signature: &Signature) -> bool {
    let modulus = constants::L;
    let order_check_pk = self.0.mul(modulus);
    if !order_check_pk.eq(&Gs::identity()) {
      return false;
    }

    let order_check_r = signature.r.mul(modulus);
    if !order_check_r.eq(&Gs::identity()) {
      return false;
    }

    // 0 = -S . P_G + R + c . pk
    self
      .0
      .mul(c)
      .add(signature.r)
      .add(BASEPOINT.mul(signature.s).neg())
      .eq(&Gs::identity())
  }
}
