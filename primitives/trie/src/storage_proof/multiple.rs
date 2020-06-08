// Copyright 2020 Parity Technologies (UK) Ltd.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// ! Trie storage proofs allowing using different proofs.

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

	/// Kind for `MultipleStorageProof::TrieSkipHashes`.
	TrieSkipHashes = 2,
	
	/// Kind for `MultipleStorageProof::FullForMerge`.
	FullForMerge = 126,

	/// Kind for `MultipleStorageProof::QueryPlan`.
	KnownQueryPlanAndValues = 127,
}

impl StorageProofKind {
	/// Decode a byte value representing the storage kind.
	/// Return `None` if the kind does not exists or is not allowed.
	pub fn from_byte(encoded: u8) -> Option<Self> {
		Some(match encoded {
			x if x == StorageProofKind::Flat as u8 => StorageProofKind::Flat,
			x if x == StorageProofKind::TrieSkipHashes as u8 => StorageProofKind::TrieSkipHashes,
			x if x == StorageProofKind::FullForMerge as u8 => StorageProofKind::FullForMerge,
			x if x == StorageProofKind::KnownQueryPlanAndValues as u8 => StorageProofKind::KnownQueryPlanAndValues,
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
	TrieSkipHashes(super::compact::Flat<crate::Layout<H>>, PhantomData<D>),

	/// See `crate::storage_proof::compact::FullForMerge`.
	///
	/// This variant is temporary to allow producing known query proof over
	/// substrate state machine, until it can be configured over a specific
	/// proving backend.
	/// The fundamental flaw here is that this leads to a partial implementation
	/// of the proof verification.
	FullForMerge(super::compact::FullForMerge),

	/// See `crate::storage_proof::query_plan::KnownQueryPlanAndValues`.
	///
	/// This variant is temporary to allow producing known query proof over
	/// substrate state machine, until it can be configured over a specific
	/// proving backend.
	/// The fundamental flaw here is that this leads to a partial implementation
	/// of the proof verification.
	KnownQueryPlanAndValues(super::query_plan::KnownQueryPlanAndValues<crate::Layout<H>>),
}

impl<H, D> sp_std::fmt::Debug for MultipleStorageProof<H, D> {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		match self {
			MultipleStorageProof::Flat(v) => v.fmt(f),
			MultipleStorageProof::TrieSkipHashes(v, _) => v.fmt(f),
			MultipleStorageProof::FullForMerge(v) => v.fmt(f),
			MultipleStorageProof::KnownQueryPlanAndValues(v) => v.fmt(f),
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
				StorageProofKind::TrieSkipHashes => MultipleStorageProof::TrieSkipHashes(
					Decode::decode(value)?,
					PhantomData,
				),
				StorageProofKind::FullForMerge => MultipleStorageProof::FullForMerge(Decode::decode(value)?),
				StorageProofKind::KnownQueryPlanAndValues => MultipleStorageProof::KnownQueryPlanAndValues(
					Decode::decode(value)?
				),
		})
	}
}

impl<H, D> Encode for MultipleStorageProof<H, D> {
	fn encode_to<T: CodecOutput>(&self, dest: &mut T) {
		(self.kind() as u8).encode_to(dest);
		match self {
			MultipleStorageProof::Flat(p) => p.encode_to(dest),
			MultipleStorageProof::TrieSkipHashes(p, _) => p.encode_to(dest),
			MultipleStorageProof::FullForMerge(p) => p.encode_to(dest),
			MultipleStorageProof::KnownQueryPlanAndValues(p) => p.encode_to(dest),
		}
	}
}

impl<H, D: DefaultKind> StorageProof for MultipleStorageProof<H, D> {
	fn empty() -> Self {
		match D::KIND {
			StorageProofKind::Flat =>
				MultipleStorageProof::Flat(super::simple::Flat::empty()),
			StorageProofKind::TrieSkipHashes =>
				MultipleStorageProof::TrieSkipHashes(super::compact::Flat::empty(), PhantomData),
			StorageProofKind::FullForMerge =>
				MultipleStorageProof::FullForMerge(super::compact::FullForMerge::empty()),
			StorageProofKind::KnownQueryPlanAndValues => MultipleStorageProof::KnownQueryPlanAndValues(
				super::query_plan::KnownQueryPlanAndValues::empty()
			),
		}
	}


	fn is_empty(&self) -> bool {
		match self {
			MultipleStorageProof::Flat(data) => data.is_empty(),
			MultipleStorageProof::TrieSkipHashes(data, _) => data.is_empty(),
			MultipleStorageProof::FullForMerge(data) => data.is_empty(),
			MultipleStorageProof::KnownQueryPlanAndValues(data) => data.is_empty(),
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
			StorageProofKind::TrieSkipHashes => MultipleRecorder::Full(Default::default(), D::KIND),
			StorageProofKind::FullForMerge => MultipleRecorder::Full(Default::default(), D::KIND),
			StorageProofKind::KnownQueryPlanAndValues => MultipleRecorder::Full(Default::default(), D::KIND),
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
		match self {
			MultipleRecorder::Flat(data, kind, _) => MultipleRecorder::Flat(data.clone(), *kind, PhantomData),
			MultipleRecorder::Full(data, kind) => MultipleRecorder::Full(data.clone(), *kind),
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

// TODO EMCH can remove Default bound with manual impl on recorder
impl<H, D: DefaultKind> RegStorageProof<H> for MultipleStorageProof<H, D>
	where
		H: Hasher,
		H::Out: Codec,
		D: DefaultKind,
{
	// Actually one could ignore this if he knows its type to be non compact.
	// TODO EMCH try a const function over D, this have very little chance to work
	// Maybe switch that to Option so we can put it to None here as it is variable
	const INPUT_KIND: InputKind = InputKind::ChildTrieRoots;

	type RecordBackend = MultipleRecorder<H, D>;

	fn extract_proof(recorder: &Self::RecordBackend, input: Input) -> Result<Self> {
		match recorder.target() {
			StorageProofKind::Flat => {
				if let MultipleRecorder::Flat(rec, _, _) = recorder {
					return Ok(MultipleStorageProof::Flat(super::simple::Flat::extract_proof(rec, input)?))
				}
			},
			StorageProofKind::TrieSkipHashes => {
				if let MultipleRecorder::Full(rec, _) = recorder {
					return Ok(MultipleStorageProof::TrieSkipHashes(
						super::compact::Flat::extract_proof(rec, input)?,
						PhantomData,
					))
				}
			},
			StorageProofKind::FullForMerge => {
				if let MultipleRecorder::Full(rec, _) = recorder {
					return Ok(MultipleStorageProof::FullForMerge(
						super::compact::FullForMerge::extract_proof(rec, input)?,
					))
				}
			},
			StorageProofKind::KnownQueryPlanAndValues => {
				if let MultipleRecorder::Full(rec, _) = recorder {
					return Ok(MultipleStorageProof::KnownQueryPlanAndValues(
						super::query_plan::KnownQueryPlanAndValues::extract_proof(rec, input)?,
					))
				}
			},
		}
		Err(missing_pack_input())
	}
}

impl<H, D> BackendStorageProof<H> for MultipleStorageProof<H, D>
	where
		H: Hasher,
		H::Out: Codec,
		D: DefaultKind,
{
	type StorageProofReg = super::compact::FullForMerge;
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
			MultipleStorageProof::TrieSkipHashes(p, _) => Ok(p),
			_ => Err(incompatible_type()),
		}
	}
}

impl<H, D> TryInto<super::compact::FullForMerge> for MultipleStorageProof<H, D> {
	type Error = super::Error;

	fn try_into(self) -> Result<super::compact::FullForMerge> {
		match self {
			MultipleStorageProof::FullForMerge(p) => Ok(p),
			_ => Err(incompatible_type()),
		}
	}
}

impl<H, D> TryInto<super::query_plan::KnownQueryPlanAndValues<Layout<H>>> for MultipleStorageProof<H, D> {
	type Error = super::Error;

	fn try_into(self) -> Result<super::query_plan::KnownQueryPlanAndValues<Layout<H>>> {
		match self {
			MultipleStorageProof::KnownQueryPlanAndValues(p) => Ok(p),
			_ => Err(incompatible_type()),
		}
	}
}

impl<H, D> MultipleStorageProof<H, D> {
	/// Get kind type for the storage proof variant.
	pub fn kind(&self) -> StorageProofKind {
		match self {
			MultipleStorageProof::Flat(_) => StorageProofKind::Flat,
			MultipleStorageProof::TrieSkipHashes(_, _) => StorageProofKind::TrieSkipHashes,
			MultipleStorageProof::FullForMerge(_) => StorageProofKind::FullForMerge,
			MultipleStorageProof::KnownQueryPlanAndValues(_) => StorageProofKind::KnownQueryPlanAndValues,
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
			StorageProofKind::TrieSkipHashes => MultipleStorageProof::TrieSkipHashes(self.into(), PhantomData),
			StorageProofKind::FullForMerge => MultipleStorageProof::FullForMerge(self),
			// we cannot convert, actually this should not be in storage proof kind TODO EMCH
			// this was only here to be able to product query plan without using different backend.
			// User shall therefore register and try into: but target is that user uses the query_plan
			// backend.
			StorageProofKind::KnownQueryPlanAndValues => MultipleStorageProof::FullForMerge(self),
		}
	}
}


/*
	/// Can also fail on invalid compact proof.
	pub fn into_partial_db<H>(self) -> Result<ChildrenProofMap<MemoryDB<H>>>
	where
		H: Hasher,
		H::Out: Decode,
	{
		let mut result = ChildrenProofMap::default();
		match self {
			s@MultipleStorageProof::Flat(..) => {
				let db = s.into_partial_flat_db::<H>()?;
				result.insert(ChildInfoProof::top_trie(), db);
			},
			MultipleStorageProof::Full(children) => {
				for (child_info, proof) in children.into_iter() {
					let mut db = MemoryDB::default();
					for item in proof.into_iter() {
						db.insert(EMPTY_PREFIX, &item);
					}
					result.insert(child_info, db);
				}
			},
			MultipleStorageProof::TrieSkipHashesForMerge(children) => {
				for (child_info, (proof, _root)) in children.into_iter() {
					let mut db = MemoryDB::default();
					for (key, value) in proof.0.into_iter() {
						let key = Decode::decode(&mut &key[..])?;
						db.emplace(key, EMPTY_PREFIX, value);
					}
					result.insert(child_info, db);
				}
			},
			MultipleStorageProof::TrieSkipHashesFull(children) => {
				for (child_info, proof) in children.into_iter() {
					// Note that this does check all hashes so using a trie backend
					// for further check is not really good (could use a direct value backend).
					let (_root, db) = crate::unpack_proof_to_memdb::<Layout<H>>(proof.as_slice())?;
					result.insert(child_info, db);
				}
			},
			s@MultipleStorageProof::TrieSkipHashes(..) => {
				let db = s.into_partial_flat_db::<H>()?;
				result.insert(ChildInfoProof::top_trie(), db);
			},
			MultipleStorageProof::KnownQueryPlanAndValues(_children) => {
				return Err(no_partial_db_support());
			},
		}
		Ok(result)
	}

	/// Create in-memory storage of proof check backend.
	///
	/// Behave similarily to `into_partial_db`.
	pub fn into_partial_flat_db<H>(self) -> Result<MemoryDB<H>>
	where
		H: Hasher,
		H::Out: Decode,
	{
		let mut db = MemoryDB::default();
		let mut db_empty = true;
		match self {
			s@MultipleStorageProof::Flat(..) => {
				for item in s.iter_nodes_flatten() {
					db.insert(EMPTY_PREFIX, &item[..]);
				}
			},
			MultipleStorageProof::Full(children) => {
				for (_child_info, proof) in children.into_iter() {
					for item in proof.into_iter() {
						db.insert(EMPTY_PREFIX, &item);
					}
				}
			},
			MultipleStorageProof::TrieSkipHashesForMerge(children) => {
				for (_child_info, (proof, _root)) in children.into_iter() {
					for (key, value) in proof.0.into_iter() {
						let key = Decode::decode(&mut &key[..])?;
						db.emplace(key, EMPTY_PREFIX, value);
					}
				}
			},
			MultipleStorageProof::TrieSkipHashesFull(children) => {
				for (_child_info, proof) in children.into_iter() {
					// Note that this does check all hashes so using a trie backend
					// for further check is not really good (could use a direct value backend).
					let (_root, child_db) = crate::unpack_proof_to_memdb::<Layout<H>>(proof.as_slice())?;
					if db_empty {
						db_empty = false;
						db = child_db;
					} else {
						db.consolidate(child_db);
					}
				}
			},
			MultipleStorageProof::TrieSkipHashes(children) => {
				for proof in children.into_iter() {
					let (_root, child_db) = crate::unpack_proof_to_memdb::<Layout<H>>(proof.as_slice())?;
					if db_empty {
						db_empty = false;
						db = child_db;
					} else {
						db.consolidate(child_db);
					}
				}
			},
			MultipleStorageProof::KnownQueryPlanAndValues(_children) => {
				return Err(no_partial_db_support());
			},
		}
		Ok(db)
	}
*/
