use data_encoding::HEXLOWER;
use p256::{
  elliptic_curve::hash2field::{hash_to_field, ExpandMsgXmd},
  ProjectivePoint, Scalar,
};
use rand_core_latest::OsRng;
use rand_latest::RngCore;
use rug::Integer;
use sha2::Sha256;

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

type P = p256::ProjectivePoint;
type S = p256::Scalar;
use curveP256::P256Scalar as F;

mod keys_p256;
use crate::keys_p256::{PublicKey, SecretKey};

fn int(bytes: &[u8]) -> Integer {
  Integer::from_str_radix(&HEXLOWER.encode(&bytes), 16).unwrap()
}

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
      println!("z.ru: {:?}", int(&ru.get_value().unwrap().to_repr()));
      println!("z.rv: {:?}", int(&rv.get_value().unwrap().to_repr()));
    }
    _ => print!(""),
  }

  let c_bits = s_to_bits::<F, _>(&mut cs, c, "c bits")?;
  let pk = alloc_point::<F, _>(&mut cs, "PK", pkx, pky)?;
  let cpk = pk.scalar_mul(&mut cs.namespace(|| "[c]PK"), c_bits)?;

  let (cpk_x, cpk_y, _) = cpk.get_coordinates();
  match cpk_x.get_value() {
    Some(_) => {
      println!("z.cpk_x: {:?}", int(&cpk_x.get_value().unwrap().to_repr()));
      println!("z.cpk_y: {:?}", int(&cpk_y.get_value().unwrap().to_repr()));
    }
    _ => print!(""),
  }

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

#[allow(non_snake_case)]
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

  let cpk = pk.0 * c;
  let (cpkxf, cpkyf) = cpk.to_affine().coordinates();
  println!("m.cpkxf: {}", int(&cpkxf.to_bytes()));
  println!("m.cpkyf: {}", int(&cpkyf.to_bytes()));

  let signature = sk.sign_commitment(c, &mut OsRng);
  assert!(pk.verify_commitment(c, &signature));

  let (gxf, gyf) = ProjectivePoint::GENERATOR.to_affine().coordinates();
  let (gx, gy) = (
    Scalar::from_repr(gxf.to_bytes()).unwrap(),
    Scalar::from_repr(gyf.to_bytes()).unwrap(),
  );

  // println!("z.gx: {}", int(&gxf.to_bytes()));
  // println!("z.gy: {}", int(&gyf.to_bytes()));

  let (rxf, ryf) = signature.r.to_affine().coordinates();
  let (rx, ry) = (
    Scalar::from_repr(rxf.to_bytes()).unwrap(),
    Scalar::from_repr(ryf.to_bytes()).unwrap(),
  );

  println!("z.rxf: {}", int(&rxf.to_bytes()));
  println!("z.rx: {}", int(&rx.to_bytes()));
  println!("z.ryf: {}", int(&ryf.to_bytes()));
  println!("z.ry: {}", int(&ry.to_bytes()));

  let (pkxf, pkyf) = pk.0.to_affine().coordinates();
  let (pkx, pky) = (
    Scalar::from_repr(pkxf.to_bytes()).unwrap(),
    Scalar::from_repr(pkyf.to_bytes()).unwrap(),
  );

  let s = signature.s;

  println!("z.s: {}", int(&s.to_bytes()));

  let mut cs: ShapeCS<P> = ShapeCS::new();

  let I = S::ONE;
  let _ = synthesize_sign_commitment::<F, _>(
    &mut cs.namespace(|| "synthesize"),
    F(rx),
    F(ry),
    F(gx),
    F(gy),
    F(pkx),
    F(pky),
    F(c),
    F(s),
    F(I),
  )
  .unwrap();

  println!("Number of constraints: {}", cs.num_constraints());

  let shape = cs.r1cs_shape();
  let gens = cs.r1cs_gens();

  let mut S1 = SatisfyingAssignment::<P>::new();
  let _ = synthesize_sign_commitment::<F, _>(
    &mut S1.namespace(|| "synthesize"),
    F(rx),
    F(ry),
    F(gx),
    F(gy),
    F(pkx),
    F(pky),
    F(c),
    F(s),
    F(I),
  )
  .unwrap();

  let (U1, W1) = S1.r1cs_instance_and_witness(&shape, &gens).unwrap();
  assert!(shape.is_sat(&gens, &U1, &W1).is_ok());
}
