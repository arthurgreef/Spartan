use crate::errors::R1CSError;
use crate::traits::{Group, CompressedGroup};

use super::group::{GroupElement, VartimeMultiscalarMul, GROUP_BASEPOINT_COMPRESSED};
use super::scalar::Scalar;
use digest::{ExtendableOutput, Input};
use merlin::Transcript;
use sha3::Shake256;
use std::io::Read;
use core::{
  fmt::Debug,
  marker::PhantomData,
  ops::{Add, AddAssign, Mul, MulAssign},
};

#[derive(Debug)]
pub struct MultiCommitGens {
  pub n: usize,
  pub G: Vec<GroupElement>,
  pub h: GroupElement,
}

impl MultiCommitGens {
  pub fn new(n: usize, label: &[u8]) -> Self {
    let mut shake = Shake256::default();
    shake.input(label);
    shake.input(GROUP_BASEPOINT_COMPRESSED.as_bytes());

    let mut reader = shake.xof_result();
    let mut gens: Vec<GroupElement> = Vec::new();
    let mut uniform_bytes = [0u8; 64];
    for _ in 0..n + 1 {
      reader.read_exact(&mut uniform_bytes).unwrap();
      gens.push(GroupElement::from_uniform_bytes(&uniform_bytes));
    }

    MultiCommitGens {
      n,
      G: gens[..n].to_vec(),
      h: gens[n],
    }
  }

  pub fn clone(&self) -> MultiCommitGens {
    MultiCommitGens {
      n: self.n,
      h: self.h,
      G: self.G.clone(),
    }
  }

  pub fn split_at(&self, mid: usize) -> (MultiCommitGens, MultiCommitGens) {
    let (G1, G2) = self.G.split_at(mid);

    (
      MultiCommitGens {
        n: G1.len(),
        G: G1.to_vec(),
        h: self.h,
      },
      MultiCommitGens {
        n: G2.len(),
        G: G2.to_vec(),
        h: self.h,
      },
    )
  }
}

pub trait Commitments {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> GroupElement;
}

impl Commitments for Scalar {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> GroupElement {
    assert_eq!(gens_n.n, 1);
    GroupElement::vartime_multiscalar_mul(&[*self, *blind], &[gens_n.G[0], gens_n.h])
  }
}

impl Commitments for Vec<Scalar> {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> GroupElement {
    assert_eq!(gens_n.n, self.len());
    GroupElement::vartime_multiscalar_mul(self, &gens_n.G) + blind * gens_n.h
  }
}

impl Commitments for [Scalar] {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> GroupElement {
    assert_eq!(gens_n.n, self.len());
    GroupElement::vartime_multiscalar_mul(self, &gens_n.G) + blind * gens_n.h
  }
}

#[derive(Debug)]
pub struct CommitGens<G: Group> {
  gens: Vec<G::PreprocessedGroupElement>,
  _p: PhantomData<G>,
}

impl<G: Group> CommitGens<G> {
  pub fn new(label: &[u8], n: usize) -> Self {
    let mut shake = Shake256::default();
    shake.input(label);
    let mut reader = shake.xof_result();
    let mut gens: Vec<G::PreprocessedGroupElement> = Vec::new();
    let mut uniform_bytes = [0u8; 64];
    for _ in 0..n {
      reader.read_exact(&mut uniform_bytes).unwrap();
      gens.push(G::from_uniform_bytes(&uniform_bytes).unwrap());
    }

    CommitGens {
      gens,
      _p: PhantomData::default(),
    }
  }
}

pub trait CommitTrait<G: Group> {
  fn commit(&self, gens: &CommitGens<G>) -> Commitment<G>;
}

impl<G: Group> CommitTrait<G> for [G::Scalar] {
  fn commit(&self, gens: &CommitGens<G>) -> Commitment<G> {
    assert!(gens.gens.len() >= self.len());
    Commitment {
      comm: G::vartime_multiscalar_mul(self, &gens.gens[..self.len()]),
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Commitment<G: Group> {
  pub(crate) comm: G,
}

impl<G: Group> Commitment<G> {
  pub fn compress(&self) -> CompressedCommitment<G::CompressedGroupElement> {
    CompressedCommitment {
      comm: self.comm.compress(),
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompressedCommitment<C: CompressedGroup> {
  comm: C,
}

impl<C: CompressedGroup> CompressedCommitment<C> {
  pub fn decompress(&self) -> Result<Commitment<C::GroupElement>, R1CSError> {
    let comm = self.comm.decompress();
    if comm.is_none() {
      return Err(R1CSError::DecompressionError);
    }
    Ok(Commitment {
      comm: comm.unwrap(),
    })
  }
}

pub trait AppendToTranscriptTrait {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript);
}

impl<G: Group> AppendToTranscriptTrait for Commitment<G> {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(label, self.comm.compress().as_bytes());
  }
}

impl<C: CompressedGroup> AppendToTranscriptTrait for CompressedCommitment<C> {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(label, self.comm.as_bytes());
  }
}

impl<'b, G: Group> MulAssign<&'b G::Scalar> for Commitment<G> {
  fn mul_assign(&mut self, scalar: &'b G::Scalar) {
    let result = (self as &Commitment<G>).comm * scalar;
    *self = Commitment { comm: result };
  }
}

impl<'a, 'b, G: Group> Mul<&'b G::Scalar> for &'a Commitment<G> {
  type Output = Commitment<G>;
  fn mul(self, scalar: &'b G::Scalar) -> Commitment<G> {
    Commitment {
      comm: self.comm * scalar,
    }
  }
}

impl<G: Group> Mul<G::Scalar> for Commitment<G> {
  type Output = Commitment<G>;

  fn mul(self, scalar: G::Scalar) -> Commitment<G> {
    Commitment {
      comm: self.comm * scalar,
    }
  }
}

impl<'b, G: Group> AddAssign<&'b Commitment<G>> for Commitment<G> {
  fn add_assign(&mut self, other: &'b Commitment<G>) {
    let result = (self as &Commitment<G>).comm + other.comm;
    *self = Commitment { comm: result };
  }
}

impl<'a, 'b, G: Group> Add<&'b Commitment<G>> for &'a Commitment<G> {
  type Output = Commitment<G>;
  fn add(self, other: &'b Commitment<G>) -> Commitment<G> {
    Commitment {
      comm: self.comm + other.comm,
    }
  }
}

macro_rules! define_add_variants {
  (G = $g:path, LHS = $lhs:ty, RHS = $rhs:ty, Output = $out:ty) => {
    impl<'b, G: $g> Add<&'b $rhs> for $lhs {
      type Output = $out;
      fn add(self, rhs: &'b $rhs) -> $out {
        &self + rhs
      }
    }

    impl<'a, G: $g> Add<$rhs> for &'a $lhs {
      type Output = $out;
      fn add(self, rhs: $rhs) -> $out {
        self + &rhs
      }
    }

    impl<G: $g> Add<$rhs> for $lhs {
      type Output = $out;
      fn add(self, rhs: $rhs) -> $out {
        &self + &rhs
      }
    }
  };
}

macro_rules! define_add_assign_variants {
  (G = $g:path, LHS = $lhs:ty, RHS = $rhs:ty) => {
    impl<G: $g> AddAssign<$rhs> for $lhs {
      fn add_assign(&mut self, rhs: $rhs) {
        *self += &rhs;
      }
    }
  };
}

define_add_assign_variants!(G = Group, LHS = Commitment<G>, RHS = Commitment<G>);
define_add_variants!(G = Group, LHS = Commitment<G>, RHS = Commitment<G>, Output = Commitment<G>);
