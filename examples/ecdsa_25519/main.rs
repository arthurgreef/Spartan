use curve25519_dalek::constants::{ED25519_BASEPOINT_POINT, X25519_BASEPOINT};
use rand_core::OsRng;
use sha2::Sha512;

use bellperson::{
  gadgets::{boolean::AllocatedBit, num::AllocatedNum},
  ConstraintSystem, SynthesisError,
};
use ff::{PrimeField, PrimeFieldBits};
use libspartan::{
  bellperson::r1cs::{NovaShape, NovaWitness},
  gadgets::{ecc::AllocatedPoint, utils::alloc_num_equals},
};
use libspartan::{
  bellperson::{shape_cs::ShapeCS, solver::SatisfyingAssignment},
  curveP256,
  r1cs::{R1CSGens, R1CSShape, RelaxedR1CSInstance, RelaxedR1CSWitness},
};

type P = curve25519_dalek::edwards::EdwardsPoint;
type S = curve25519_dalek::scalar::Scalar;
use libspartan::curve25519::C25519Scalar as F;

mod keys_25519;
use crate::keys_25519::{PublicKey, SecretKey};

pub fn alloc_point<F, CS>(
  mut cs: CS,
  ns: &str,
  x: F,
  y: F,
) -> Result<AllocatedPoint<F>, SynthesisError>
where
  F: PrimeField<Repr = [u8; 32]>,
  CS: ConstraintSystem<F>,
{
  AllocatedPoint::alloc(cs.namespace(|| format!("{}xy", ns)), Some((x, y, false)))
}

pub fn s_to_bits<F, CS>(mut cs: CS, s: F, ns: &str) -> Result<Vec<AllocatedBit>, SynthesisError>
where
  F: PrimeField<Repr = [u8; 32]> + PrimeFieldBits,
  CS: ConstraintSystem<F>,
{
  let bits: Vec<AllocatedBit> = s
    .to_le_bits()
    .into_iter()
    .enumerate()
    .map(|(i, bit)| AllocatedBit::alloc(cs.namespace(|| format!("{}_bit {}", ns, i)), Some(bit)))
    .collect::<Result<Vec<AllocatedBit>, SynthesisError>>()
    .unwrap();
  Ok(bits)
}

// I know a sk such that s[G] == r[G] + [c]PK * G
#[allow(clippy::too_many_arguments)]
pub fn synthesize_sign_commitment<F, CS>(
  mut cs: CS,
  rx: F,
  ry: F,
  gx: F,
  gy: F,
  pkx: F,
  pky: F,
  c: F,
  s: F,
  io: F,
) -> Result<Option<F>, SynthesisError>
where
  F: PrimeField<Repr = [u8; 32]> + PrimeFieldBits,
  CS: ConstraintSystem<F>,
{
  let g = alloc_point::<F, _>(&mut cs, "G", gx, gy)?;
  let s_bits = s_to_bits::<F, _>(&mut cs, s, "s bits")?;
  let sg = g.scalar_mul(cs.namespace(|| "[s]G"), s_bits)?;

  let r = alloc_point::<F, _>(&mut cs, "r", rx, ry)?;

  let (ru, rv, _) = r.get_coordinates();
  match ru.get_value() {
    Some(_) => {
    println!("z.ru: {:?}", ru.get_value().unwrap().to_repr());
    println!("z.rv: {:?}", rv.get_value().unwrap().to_repr());
    },
    _ => print!(""),
  }

  let c_bits = s_to_bits::<F, _>(&mut cs, c, "c bits")?;
  let pk = alloc_point::<F, _>(&mut cs, "PK", pkx, pky)?;
  let cpk = pk.scalar_mul(&mut cs.namespace(|| "[c]PK"), c_bits)?;
  let rcpk = cpk.add(&mut cs.namespace(|| "r + [c]PK"), &r)?;

  let (rcpk_x, rcpk_y, _) = rcpk.get_coordinates();
  let (sg_x, sg_y, _) = sg.get_coordinates();

  let one = CS::one();
  cs.enforce(
    || "sg_x == rcpk_x",
    |lc| lc + rcpk_x.get_variable(),
    |lc| lc + one,
    |lc| lc + sg_x.get_variable(),
  );

  let xs_equal = alloc_num_equals(cs.namespace(|| "(sg_x == rcpk_x)?"), rcpk_x, sg_x)?;

  cs.enforce(
    || "sg_y == rcpk_y",
    |lc| lc + rcpk_y.get_variable(),
    |lc| lc + one,
    |lc| lc + sg_y.get_variable(),
  );

  let ys_equal = alloc_num_equals(cs.namespace(|| "(sg_y == rcpk_y)?"), rcpk_y, sg_y)?;

  let mut all_equal = None;
  for (i, v) in [xs_equal, ys_equal].iter().enumerate() {
    if all_equal.is_none() {
      all_equal = Some(v.clone());
    } else {
      all_equal = Some(AllocatedBit::and(
        cs.namespace(|| format!("and {}", i)),
        all_equal.as_ref().unwrap(),
        v,
      )?);
    }
  }

  let i = AllocatedNum::alloc_input(&mut cs.namespace(|| "io:i"), || Ok(io))?;
  let o = AllocatedNum::alloc_input(&mut cs.namespace(|| "io:o"), || {
    if i.get_value().unwrap() == F::one() && all_equal.unwrap().get_value().unwrap() {
      Ok(F::one())
    } else {
      Ok(F::zero())
    }
  })?;

  cs.enforce(
    || "io:i == io:o",
    |lc| lc + i.get_variable(),
    |lc| lc + one,
    |lc| lc + o.get_variable(),
  );

  Ok(o.get_value())
}

// #[allow(non_snake_case)]
// fn main() {
//   let sk = SecretKey::random();
//   let pk = PublicKey::from_secret_key(&sk);

//   let message = b"MESSAGE6_BYTES";

//   let mut digest: Vec<u8> = message.to_vec();
//   for _ in 0..(32 - message.len() as u32) {
//     digest.extend(&[0u8; 1]);
//   }

//   let c = S::hash_from_bytes::<Sha512>(digest.as_ref());

//   let signature = sk.sign_commitment(c, &mut OsRng);
//   assert!(pk.verify_commitment(c, &signature));

//   let gu = ED25519_BASEPOINT_POINT.to_montgomery();
//   assert_eq!(gu.to_bytes(), X25519_BASEPOINT.to_bytes());
//   let gx = S::from_canonical_bytes(gu.to_bytes()).unwrap();
//   let (okay, gv) = gu.to_coordinate_v();
//   assert_eq!(okay.unwrap_u8(), 1u8);
//   assert_eq!(gv, X25519_BASEPOINT.to_coordinate_v().1);
//   let gy = S::from_canonical_bytes(gv).unwrap();

//   let ru = signature.r.to_montgomery();
//   let rx = S::from_canonical_bytes(ru.to_bytes()).unwrap();
//   let (okay, rv) = ru.to_coordinate_v();
//   assert_eq!(okay.unwrap_u8(), 1u8);
//   let ry = S::from_canonical_bytes(rv).unwrap();

//   let pku = pk.0.to_montgomery();
//   let pkx = S::from_canonical_bytes(pku.to_bytes()).unwrap();
//   let (okay, pkv) = pku.to_coordinate_v();
//   assert_eq!(okay.unwrap_u8(), 1u8);
//   let pky = S::from_canonical_bytes(pkv).unwrap();
//   let s = signature.s;

//   let mut cs: ShapeCS<P> = ShapeCS::new();

//   let I = S::one();
//   let _ = synthesize_sign_commitment::<F, _>(
//     &mut cs.namespace(|| "synthesize"),
//     F(rx),
//     F(ry),
//     F(gx),
//     F(gy),
//     F(pkx),
//     F(pky),
//     F(c),
//     F(s),
//     F(I),
//   )
//   .unwrap();

//   println!("Number of constraints: {}", cs.num_constraints());

//   let shape = cs.r1cs_shape();
//   let gens = cs.r1cs_gens();

//   let mut S1 = SatisfyingAssignment::<P>::new();
//   let _ = synthesize_sign_commitment::<F, _>(
//     &mut S1.namespace(|| "synthesize"),
//     F(rx),
//     F(ry),
//     F(gx),
//     F(gy),
//     F(pkx),
//     F(pky),
//     F(c),
//     F(s),
//     F(I),
//   )
//   .unwrap();

//   let (U1, W1) = S1.r1cs_instance_and_witness(&shape, &gens).unwrap();
//   assert!(shape.is_sat(&gens, &U1, &W1).is_ok());
// }
