// Copyright 2020 Parity Technologies (UK) Ltd.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// ! Enumeration to use different storage proofs from a single type.

use super::*;
use sp_std::convert::TryInto;
use sp_std::marker::PhantomData;

/// Different kind of proof representation are allowed.
/// This definition is used as input parameter when producing
/// a storage proof.
/// Some kind are reserved for test or internal use and will
/// not be usable when decoding proof, those could be remove
/// when substrate will be able to define custom state-machine
/// backend.
#[repr(u8)]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum StorageProofKind {
	/// Kind for `MultipleStorageProof::Flat`.
	Flat = 1,

	/// Kind for `MultipleStorageProof::Compact`.
	Compact = 2,
}

impl StorageProofKind {
	/// Decode a byte value representing the storage kind.
	/// Return `None` if the kind does not exists or is not allowed.
	pub fn from_byte(encoded: u8) -> Option<Self> {
		Some(match encoded {
			x if x == StorageProofKind::Flat as u8 => StorageProofKind::Flat,
			x if x == StorageProofKind::Compact as u8 => StorageProofKind::Compact,
			_ => return None,
		})
	}
}

/// Allow usage of multiple proof at the same time. This is usefull when
/// we want to be able to operate from different proof origin.
/// It produces a single proof type that is defined by type parameter `D`
/// as `DefaultKind`.
#[derive(PartialEq, Eq, Clone)]
pub enum MultipleStorageProof<H, D> {
	/// See `crate::storage_proof::simple::Flat`.
	Flat(super::simple::Flat),

	/// See `crate::storage_proof::compact::Flat`.
	Compact(super::compact::Flat<crate::Layout<H>>, PhantomData<D>),
}

impl<H, D> sp_std::fmt::Debug for MultipleStorageProof<H, D> {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		match self {
			MultipleStorageProof::Flat(v) => v.fmt(f),
			MultipleStorageProof::Compact(v, _) => v.fmt(f),
		}
	}
}

/// Allow to use specific kind of proof by default.
pub trait DefaultKind: Clone + Send + Sync {
	const KIND: StorageProofKind;
}

/// Default the multiple proof to flat.
#[derive(Clone, Copy)]
pub struct FlatDefault;

impl DefaultKind for FlatDefault {
	const KIND: StorageProofKind = StorageProofKind::Flat;
}

impl<H, D> Decode for MultipleStorageProof<H, D> {
	fn decode<I: CodecInput>(value: &mut I) -> CodecResult<Self> {
		let kind = value.read_byte()?;
		Ok(match StorageProofKind::from_byte(kind)
			.ok_or_else(|| codec::Error::from("Invalid storage kind"))? {
				StorageProofKind::Flat => MultipleStorageProof::Flat(Decode::decode(value)?),
				StorageProofKind::Compact => MultipleStorageProof::Compact(
					Decode::decode(value)?,
					PhantomData,
				),
		})
	}
}

impl<H, D> Encode for MultipleStorageProof<H, D> {
	fn encode_to<T: CodecOutput>(&self, dest: &mut T) {
		(self.kind() as u8).encode_to(dest);
		match self {
			MultipleStorageProof::Flat(p) => p.encode_to(dest),
			MultipleStorageProof::Compact(p, _) => p.encode_to(dest),
		}
	}
}

impl<H, D: DefaultKind> Common for MultipleStorageProof<H, D> {
	fn empty() -> Self {
		match D::KIND {
			StorageProofKind::Flat =>
				MultipleStorageProof::Flat(super::simple::Flat::empty()),
			StorageProofKind::Compact =>
				MultipleStorageProof::Compact(super::compact::Flat::empty(), PhantomData),
		}
	}

	fn is_empty(&self) -> bool {
		match self {
			MultipleStorageProof::Flat(data) => data.is_empty(),
			MultipleStorageProof::Compact(data, _) => data.is_empty(),
		}
	}
}

pub enum MultipleRecorder<H: Hasher, D> {
	Flat(super::FlatRecorder<H>, StorageProofKind, PhantomData<D>),
	Full(super::FullRecorder<H>, StorageProofKind),
}

impl<H: Hasher, D: DefaultKind> MultipleRecorder<H, D> {
	/// Instantiate a recorder of a given type.
	pub fn new_recorder(kind: StorageProofKind) -> Self {
		match kind {
			StorageProofKind::Flat => MultipleRecorder::Flat(Default::default(), D::KIND, PhantomData),
			StorageProofKind::Compact => MultipleRecorder::Full(Default::default(), D::KIND),
		}
	}

	/// Targetted storage proof kind.
	pub fn target(&self) -> StorageProofKind {
		match self {
			MultipleRecorder::Flat(_, k, _) => *k,
			MultipleRecorder::Full(_, k) => *k,
		}
	}
}

impl<H: Hasher, D: DefaultKind> Default for MultipleRecorder<H, D> {
	fn default() -> Self {
		Self::new_recorder(D::KIND)
	}
}

impl<H: Hasher, D> Clone for MultipleRecorder<H, D> {
	fn clone(&self) -> Self {
		use MultipleRecorder::{Flat, Full};
		match self {
			Flat(data, kind, _) => Flat(data.clone(), *kind, PhantomData),
			Full(data, kind) => Full(data.clone(), *kind),
		}
	}
}

impl<H: Hasher, D: DefaultKind> RecordBackend<H> for MultipleRecorder<H, D> {
	fn get(&self, child_info: &ChildInfo, key: &H::Out) -> Option<Option<DBValue>> {
		match self {
			MultipleRecorder::Flat(rec, _ ,_) => rec.get(child_info, key),
			MultipleRecorder::Full(rec, _) => rec.get(child_info, key),
		}
	}

	fn record(&mut self, child_info: ChildInfo, key: H::Out, value: Option<DBValue>) {
		match self {
			MultipleRecorder::Flat(rec, _, _) => rec.record(child_info, key, value),
			MultipleRecorder::Full(rec, _) => rec.record(child_info, key, value),
		}
	}

	fn merge(&mut self, other: Self) -> bool {
		match self {
			MultipleRecorder::Flat(rec, _, _) => {
				match other {
					MultipleRecorder::Flat(oth, _, _) => {
						rec.merge(oth);
						true
					},
					_ => false
				}
			},
			MultipleRecorder::Full(rec, _) => {
				match other {
					MultipleRecorder::Full(oth, _) => {
						rec.merge(oth);
						true
					},
					_ => false,
				}
			},
		}
	}
}

impl<H, D: DefaultKind> Recordable<H> for MultipleStorageProof<H, D>
	where
		H: Hasher,
		H::Out: Codec,
		D: DefaultKind,
{
	// This could be ignored in case it is knowned that the type is not compact.
	const INPUT_KIND: InputKind = InputKind::ChildTrieRoots;

	type RecordBackend = MultipleRecorder<H, D>;

	fn extract_proof(recorder: &Self::RecordBackend, input: Input) -> Result<Self> {
		match recorder.target() {
			StorageProofKind::Flat => {
				if let MultipleRecorder::Flat(rec, _, _) = recorder {
					return Ok(MultipleStorageProof::Flat(super::simple::Flat::extract_proof(rec, input)?))
				}
			},
			StorageProofKind::Compact => {
				if let MultipleRecorder::Full(rec, _) = recorder {
					return Ok(MultipleStorageProof::Compact(
						super::compact::Flat::extract_proof(rec, input)?,
						PhantomData,
					))
				}
			},
		}
		Err(missing_pack_input())
	}
}

impl<H, D> BackendProof<H> for MultipleStorageProof<H, D>
	where
		H: Hasher,
		H::Out: Codec,
		D: DefaultKind,
{
	type ProofRaw = super::compact::FullForMerge;

	fn into_partial_db(self) -> Result<MemoryDB<H>> {
		match self {
			MultipleStorageProof::Flat(p) => p.into_partial_db(),
			MultipleStorageProof::Compact(p, _) => p.into_partial_db(),
		}
	}

}

impl<H, D> TryInto<super::simple::Flat> for MultipleStorageProof<H, D> {
	type Error = super::Error;

	fn try_into(self) -> Result<super::simple::Flat> {
		match self {
			MultipleStorageProof::Flat(p) => Ok(p),
			_ => Err(incompatible_type()),
		}
	}
}

impl<H, D> TryInto<super::compact::Flat<Layout<H>>> for MultipleStorageProof<H, D> {
	type Error = super::Error;

	fn try_into(self) -> Result<super::compact::Flat<Layout<H>>> {
		match self {
			MultipleStorageProof::Compact(p, _) => Ok(p),
			_ => Err(incompatible_type()),
		}
	}
}

impl<H, D> MultipleStorageProof<H, D> {
	/// Get kind type for the storage proof variant.
	pub fn kind(&self) -> StorageProofKind {
		match self {
			MultipleStorageProof::Flat(_) => StorageProofKind::Flat,
			MultipleStorageProof::Compact(_, _) => StorageProofKind::Compact,
		}
	}
}

impl<H: Hasher, D: DefaultKind> Into<MultipleStorageProof<H, D>> for super::compact::FullForMerge
	where
		H::Out: Codec,
{
	fn into(self) -> MultipleStorageProof<H, D> {
		match D::KIND {
			StorageProofKind::Flat => MultipleStorageProof::Flat(self.into()),
			StorageProofKind::Compact => MultipleStorageProof::Compact(self.into(), PhantomData),
		}
	}
}
