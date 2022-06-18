extern crate rand;
extern crate zerocaf;

mod keys_25519;

// use std::fs::File;
// use std::io::Write;

use bellperson::{
  gadgets::{boolean::AllocatedBit, num::AllocatedNum},
  ConstraintSystem, SynthesisError,
};
use ff::{Field, PrimeField, PrimeFieldBits};
use libspartan::{
  bellperson::{
    r1cs::{SpartanShape, SpartanWitness},
    shape_cs::ShapeCS,
    solver::SatisfyingAssignment,
  },
  curve25519::{self},
  gadgets::{ecc_twist::AllocatedPointTwist, utils::alloc_num_equals},
  Assignment, Instance, SNARKGens, SNARK,
};

use merlin::Transcript;
use sha2::Sha512;
use zerocaf::{
  //backend::u64::constants,
  constants::BASEPOINT,
  edwards::{AffinePoint},
  traits::ValidityCheck,
};

use crate::keys_25519::{PublicKey, SecretKey};

pub(crate) type Gs = zerocaf::edwards::EdwardsPoint;
pub(crate) type Fps = zerocaf::field::FieldElement;
pub(crate) type Fqs = zerocaf::scalar::Scalar;
pub(crate) type Gd = curve25519::DEdwardsPoint;
pub(crate) type Fqd = curve25519::DScalar;

pub fn alloc_point<Fqd, Fps, CS>(
  mut cs: CS,
  ns: &str,
  px: Fps,
  py: Fps,
) -> Result<AllocatedPointTwist<Fqd>, SynthesisError>
where
  Fqd: PrimeField<Repr = [u8; 32]>,
  Fps: PrimeField<Repr = [u8; 32]>,
  CS: ConstraintSystem<Fqd>,
{
  let x = Fqd::from_repr(px.to_repr()).unwrap();
  let y = Fqd::from_repr(py.to_repr()).unwrap();

  AllocatedPointTwist::alloc(cs.namespace(|| format!("{}xy", ns)), Some((x, y, false)))
}

pub fn fqs_to_bits<Fqd, Fqs, CS>(
  mut cs: CS,
  fqs: Fqs,
  ns: &str,
) -> Result<Vec<AllocatedBit>, SynthesisError>
where
  Fqd: PrimeField<Repr = [u8; 32]>,
  Fqs: PrimeField<Repr = [u8; 32]> + PrimeFieldBits,
  CS: ConstraintSystem<Fqd>,
{
  let bits: Vec<AllocatedBit> = fqs
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
pub fn synthesize_sign_commitment<Fqd, Fps, Fqs, CS>(
  mut cs: CS,
  rx: Fps,
  ry: Fps,
  gx: Fps,
  gy: Fps,
  pkx: Fps,
  pky: Fps,
  c: Fqs,
  s: Fqs,
  io: Fqd,
) -> Result<Option<Fqd>, SynthesisError>
where
  Fqd: PrimeField<Repr = [u8; 32]>,
  Fps: PrimeField<Repr = [u8; 32]>,
  Fqs: PrimeField<Repr = [u8; 32]> + PrimeFieldBits,
  CS: ConstraintSystem<Fqd>,
{
  let g = alloc_point::<Fqd, Fps, _>(&mut cs, "G", gx, gy)?;
  let s_bits = fqs_to_bits::<Fqd, Fqs, _>(&mut cs, s, "s bits")?;
  let sg = g.scalar_mul(cs.namespace(|| "[s]G"), s_bits)?;

  let (sgx, sgy, _) = sg.get_coordinates();

  // match sgx.get_value() {
  //   Some(_) => {
  //     let gx = FieldElement::from_repr(sgx.get_value().unwrap().to_repr()).unwrap();
  //     let gy = FieldElement::from_repr(sgy.get_value().unwrap().to_repr()).unwrap();
  //     println!();
  //     println!("i.g: {:?}", AffinePoint { X: gx, Y: gy });
  //   }
  //   _ => print!(""),
  // }

  let r = alloc_point::<Fqd, Fps, _>(&mut cs, "r", rx, ry)?;

  let c_bits = fqs_to_bits::<Fqd, Fqs, _>(&mut cs, c, "c bits")?;
  let pk = alloc_point::<Fqd, Fps, _>(&mut cs, "PK", pkx, pky)?;
  let cpk = pk.scalar_mul(&mut cs.namespace(|| "[c]PK"), c_bits)?;
  let rcpk = cpk.add(&mut cs.namespace(|| "r + [c]PK"), &r)?;

  let (rcpk_x, rcpk_y, _) = rcpk.get_coordinates();
  let (sg_x, sg_y, _) = sg.get_coordinates();

  // match rcpk_x.get_value() {
  //   Some(_) => {
  //     println!("rcpk_x: {:?}", rcpk_x.get_value().unwrap());
  //     println!("sgx: {:?}", sgx.get_value().unwrap());
  //     println!("rcpk_y: {:?}", rcpk_y.get_value().unwrap());
  //     println!("sg_y: {:?}", sg_y.get_value().unwrap());
  //   }
  //   _ => print!(""),
  // }

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
  let i = AllocatedNum::alloc_input(&mut cs.namespace(|| "io:i"), || Ok(io))?;

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

  let o = AllocatedNum::alloc_input(&mut cs.namespace(|| "io:o"), || {
    if i.get_value().unwrap() == Fqd::one() && all_equal.unwrap().get_value().unwrap() {
      Ok(Fqd::one())
    } else {
      Ok(Fqd::zero())
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

  let message = b"MESSAGE6_BYTES";

  let mut digest: Vec<u8> = message.to_vec();
  for _ in 0..(32 - message.len() as u32) {
    digest.extend(&[0u8; 1]);
  }

  let c = Fqs::hash_from_bytes::<Sha512>(digest.as_ref());

  let signature = sk.sign_commitment(c);
  assert!(pk.verify_commitment(c, &signature));

  let gxy = AffinePoint::from(BASEPOINT);
  assert!(gxy.is_valid().unwrap_u8() == 1u8);
  let gx = gxy.X;
  let gy = gxy.Y;

  let rxy = AffinePoint::from(signature.r);
  assert!(rxy.is_valid().unwrap_u8() == 1u8);
  let rx = rxy.X;
  let ry = rxy.Y;

  let pkxy = AffinePoint::from(pk.0);
  assert!(pkxy.is_valid().unwrap_u8() == 1u8);
  let pkx = pkxy.X;
  let pky = pkxy.Y;
  let s = signature.s;

  let mut cs: ShapeCS<Gd> = ShapeCS::new();

  let io = Fqd::one();
  let _ = synthesize_sign_commitment::<Fqd, Fps, Fqs, _>(
    &mut cs.namespace(|| "synthesize"),
    rx,
    ry,
    gx,
    gy,
    pkx,
    pky,
    c,
    s,
    io,
  )
  .unwrap();

  println!("Number of constraints: {}", cs.num_constraints());

  let shape = cs.r1cs_shape();
  let r1cs_gens = cs.r1cs_gens();

  // let list = cs.pretty_print();
  // let mut output = File::create("/mnt/wsl/PHYSICALDRIVE1p1/hashblock/Spartan/cs.txt").unwrap();
  // write!(output, "{}", list);

  let mut S = SatisfyingAssignment::<Gd>::new();
  let _ = synthesize_sign_commitment::<Fqd, Fps, Fqs, _>(
    &mut S.namespace(|| "synthesize"),
    rx,
    ry,
    gx,
    gy,
    pkx,
    pky,
    c,
    s,
    io,
  )
  .unwrap();

  let (U, W) = S.r1cs_instance_and_witness(&shape, &r1cs_gens).unwrap();
  assert!(shape.is_sat(&r1cs_gens, &U, &W).is_ok());

  let snark_gens = SNARKGens::new(shape.num_cons, shape.num_vars, shape.num_io, shape.num_cons);

  let A = shape
    .A
    .into_iter()
    .map(|(row, col, scalar)| (row, col, scalar.to_repr()))
    .collect::<Vec<(usize, usize, [u8; 32])>>();

  let B = shape
    .B
    .into_iter()
    .map(|(row, col, scalar)| (row, col, scalar.to_repr()))
    .collect::<Vec<(usize, usize, [u8; 32])>>();

  let C = shape
    .C
    .into_iter()
    .map(|(row, col, scalar)| (row, col, scalar.to_repr()))
    .collect::<Vec<(usize, usize, [u8; 32])>>();

  let inst = Instance::new(shape.num_cons, shape.num_vars, shape.num_io, &A, &B, &C).unwrap();
  let (comm, decomm) = SNARK::encode(&inst, &snark_gens);

  let s_var_asignment = S
    .aux_assignment
    .into_iter()
    .map(|scalar| scalar.to_repr())
    .collect::<Vec<[u8; 32]>>();

  let var_assignment = Assignment::new(&s_var_asignment).unwrap();

  let s_input_asignment = U.X
    .into_iter()
    .map(|scalar| scalar.to_repr())
    .collect::<Vec<[u8; 32]>>();

  let input_assignment = Assignment::new(&s_input_asignment).unwrap();

  assert!(inst.is_sat(&var_assignment, &input_assignment).is_ok());

  // produce a proof of satisfiability
  let mut prover_transcript = Transcript::new(b"snark_example");
  let proof = SNARK::prove(
    &inst,
    &comm,
    &decomm,
    var_assignment,
    &input_assignment,
    &snark_gens,
    &mut prover_transcript,
  );

  // verify the proof of satisfiability
  let mut verifier_transcript = Transcript::new(b"snark_example");
  assert!(proof
    .verify(
      &comm,
      &input_assignment,
      &mut verifier_transcript,
      &snark_gens
    )
    .is_ok());
  println!("proof verification successful!");
}
