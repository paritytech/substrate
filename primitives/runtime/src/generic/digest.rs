// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Generic implementation of a digest.

#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};

use sp_std::prelude::*;

use crate::{
	codec::{Decode, Encode, Error, Input},
	scale_info::{
		build::{Fields, Variants},
		meta_type, Path, Type, TypeInfo, TypeParameter,
	},
	ConsensusEngineId,
};
use sp_core::{ChangesTrieConfiguration, RuntimeDebug};

/// Generic header digest.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, TypeInfo)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, parity_util_mem::MallocSizeOf))]
pub struct Digest<Hash> {
	/// A list of logs in the digest.
	#[cfg_attr(
		feature = "std",
		serde(bound(serialize = "Hash: codec::Codec", deserialize = "Hash: codec::Codec"))
	)]
	pub logs: Vec<DigestItem<Hash>>,
}

impl<Item> Default for Digest<Item> {
	fn default() -> Self {
		Self { logs: Vec::new() }
	}
}

impl<Hash> Digest<Hash> {
	/// Get reference to all digest items.
	pub fn logs(&self) -> &[DigestItem<Hash>] {
		&self.logs
	}

	/// Push new digest item.
	pub fn push(&mut self, item: DigestItem<Hash>) {
		self.logs.push(item);
	}

	/// Pop a digest item.
	pub fn pop(&mut self) -> Option<DigestItem<Hash>> {
		self.logs.pop()
	}

	/// Get reference to the first digest item that matches the passed predicate.
	pub fn log<T: ?Sized, F: Fn(&DigestItem<Hash>) -> Option<&T>>(
		&self,
		predicate: F,
	) -> Option<&T> {
		self.logs().iter().find_map(predicate)
	}

	/// Get a conversion of the first digest item that successfully converts using the function.
	pub fn convert_first<T, F: Fn(&DigestItem<Hash>) -> Option<T>>(
		&self,
		predicate: F,
	) -> Option<T> {
		self.logs().iter().find_map(predicate)
	}
}

/// Digest item that is able to encode/decode 'system' digest items and
/// provide opaque access to other items.
#[derive(PartialEq, Eq, Clone, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(parity_util_mem::MallocSizeOf))]
pub enum DigestItem<Hash> {
	/// System digest item that contains the root of changes trie at given
	/// block. It is created for every block iff runtime supports changes
	/// trie creation.
	ChangesTrieRoot(Hash),

	/// A pre-runtime digest.
	///
	/// These are messages from the consensus engine to the runtime, although
	/// the consensus engine can (and should) read them itself to avoid
	/// code and state duplication. It is erroneous for a runtime to produce
	/// these, but this is not (yet) checked.
	///
	/// NOTE: the runtime is not allowed to panic or fail in an `on_initialize`
	/// call if an expected `PreRuntime` digest is not present. It is the
	/// responsibility of a external block verifier to check this. Runtime API calls
	/// will initialize the block without pre-runtime digests, so initialization
	/// cannot fail when they are missing.
	PreRuntime(ConsensusEngineId, Vec<u8>),

	/// A message from the runtime to the consensus engine. This should *never*
	/// be generated by the native code of any consensus engine, but this is not
	/// checked (yet).
	Consensus(ConsensusEngineId, Vec<u8>),

	/// Put a Seal on it. This is only used by native code, and is never seen
	/// by runtimes.
	Seal(ConsensusEngineId, Vec<u8>),

	/// Digest item that contains signal from changes tries manager to the
	/// native code.
	ChangesTrieSignal(ChangesTrieSignal),

	/// Some other thing. Unsupported and experimental.
	Other(Vec<u8>),

	/// An indication for the light clients that the runtime execution
	/// environment is updated.
	///
	/// Currently this is triggered when:
	/// 1. Runtime code blob is changed or
	/// 2. `heap_pages` value is changed.
	RuntimeEnvironmentUpdated,
}

/// Available changes trie signals.
#[derive(PartialEq, Eq, Clone, Encode, Decode, TypeInfo)]
#[cfg_attr(feature = "std", derive(Debug, parity_util_mem::MallocSizeOf))]
pub enum ChangesTrieSignal {
	/// New changes trie configuration is enacted, starting from **next block**.
	///
	/// The block that emits this signal will contain changes trie (CT) that covers
	/// blocks range [BEGIN; current block], where BEGIN is (order matters):
	/// - LAST_TOP_LEVEL_DIGEST_BLOCK+1 if top level digest CT has ever been created using current
	///   configuration AND the last top level digest CT has been created at block
	///   LAST_TOP_LEVEL_DIGEST_BLOCK;
	/// - LAST_CONFIGURATION_CHANGE_BLOCK+1 if there has been CT configuration change before and
	///   the last configuration change happened at block LAST_CONFIGURATION_CHANGE_BLOCK;
	/// - 1 otherwise.
	NewConfiguration(Option<ChangesTrieConfiguration>),
}

#[cfg(feature = "std")]
impl<Hash: Encode> serde::Serialize for DigestItem<Hash> {
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error>
	where
		S: serde::Serializer,
	{
		self.using_encoded(|bytes| sp_core::bytes::serialize(bytes, seq))
	}
}

#[cfg(feature = "std")]
impl<'a, Hash: Decode> serde::Deserialize<'a> for DigestItem<Hash> {
	fn deserialize<D>(de: D) -> Result<Self, D::Error>
	where
		D: serde::Deserializer<'a>,
	{
		let r = sp_core::bytes::deserialize(de)?;
		Decode::decode(&mut &r[..])
			.map_err(|e| serde::de::Error::custom(format!("Decode error: {}", e)))
	}
}

impl<Hash> TypeInfo for DigestItem<Hash>
where
	Hash: TypeInfo + 'static,
{
	type Identity = Self;

	fn type_info() -> Type {
		Type::builder()
			.path(Path::new("DigestItem", module_path!()))
			.type_params(vec![TypeParameter::new("Hash", Some(meta_type::<Hash>()))])
			.variant(
				Variants::new()
					.variant("ChangesTrieRoot", |v| {
						v.index(DigestItemType::ChangesTrieRoot as u8)
							.fields(Fields::unnamed().field(|f| f.ty::<Hash>().type_name("Hash")))
					})
					.variant("PreRuntime", |v| {
						v.index(DigestItemType::PreRuntime as u8).fields(
							Fields::unnamed()
								.field(|f| {
									f.ty::<ConsensusEngineId>().type_name("ConsensusEngineId")
								})
								.field(|f| f.ty::<Vec<u8>>().type_name("Vec<u8>")),
						)
					})
					.variant("Consensus", |v| {
						v.index(DigestItemType::Consensus as u8).fields(
							Fields::unnamed()
								.field(|f| {
									f.ty::<ConsensusEngineId>().type_name("ConsensusEngineId")
								})
								.field(|f| f.ty::<Vec<u8>>().type_name("Vec<u8>")),
						)
					})
					.variant("Seal", |v| {
						v.index(DigestItemType::Seal as u8).fields(
							Fields::unnamed()
								.field(|f| {
									f.ty::<ConsensusEngineId>().type_name("ConsensusEngineId")
								})
								.field(|f| f.ty::<Vec<u8>>().type_name("Vec<u8>")),
						)
					})
					.variant("ChangesTrieSignal", |v| {
						v.index(DigestItemType::ChangesTrieSignal as u8).fields(
							Fields::unnamed().field(|f| {
								f.ty::<ChangesTrieSignal>().type_name("ChangesTrieSignal")
							}),
						)
					})
					.variant("Other", |v| {
						v.index(DigestItemType::Other as u8).fields(
							Fields::unnamed().field(|f| f.ty::<Vec<u8>>().type_name("Vec<u8>")),
						)
					})
					.variant("RuntimeEnvironmentUpdated,", |v| {
						v.index(DigestItemType::RuntimeEnvironmentUpdated as u8)
							.fields(Fields::unit())
					}),
			)
	}
}

/// A 'referencing view' for digest item. Does not own its contents. Used by
/// final runtime implementations for encoding/decoding its log items.
#[derive(PartialEq, Eq, Clone, RuntimeDebug)]
pub enum DigestItemRef<'a, Hash: 'a> {
	/// Reference to `DigestItem::ChangesTrieRoot`.
	ChangesTrieRoot(&'a Hash),
	/// A pre-runtime digest.
	///
	/// These are messages from the consensus engine to the runtime, although
	/// the consensus engine can (and should) read them itself to avoid
	/// code and state duplication.  It is erroneous for a runtime to produce
	/// these, but this is not (yet) checked.
	PreRuntime(&'a ConsensusEngineId, &'a Vec<u8>),
	/// A message from the runtime to the consensus engine. This should *never*
	/// be generated by the native code of any consensus engine, but this is not
	/// checked (yet).
	Consensus(&'a ConsensusEngineId, &'a Vec<u8>),
	/// Put a Seal on it. This is only used by native code, and is never seen
	/// by runtimes.
	Seal(&'a ConsensusEngineId, &'a Vec<u8>),
	/// Digest item that contains signal from changes tries manager to the
	/// native code.
	ChangesTrieSignal(&'a ChangesTrieSignal),
	/// Any 'non-system' digest item, opaque to the native code.
	Other(&'a Vec<u8>),
	/// Runtime code or heap pages updated.
	RuntimeEnvironmentUpdated,
}

/// Type of the digest item. Used to gain explicit control over `DigestItem` encoding
/// process. We need an explicit control, because final runtimes are encoding their own
/// digest items using `DigestItemRef` type and we can't auto-derive `Decode`
/// trait for `DigestItemRef`.
#[repr(u32)]
#[derive(Encode, Decode)]
pub enum DigestItemType {
	Other = 0,
	ChangesTrieRoot = 2,
	Consensus = 4,
	Seal = 5,
	PreRuntime = 6,
	ChangesTrieSignal = 7,
	RuntimeEnvironmentUpdated = 8,
}

/// Type of a digest item that contains raw data; this also names the consensus engine ID where
/// applicable. Used to identify one or more digest items of interest.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum OpaqueDigestItemId<'a> {
	/// Type corresponding to DigestItem::PreRuntime.
	PreRuntime(&'a ConsensusEngineId),
	/// Type corresponding to DigestItem::Consensus.
	Consensus(&'a ConsensusEngineId),
	/// Type corresponding to DigestItem::Seal.
	Seal(&'a ConsensusEngineId),
	/// Some other (non-prescribed) type.
	Other,
}

impl<Hash> DigestItem<Hash> {
	/// Returns a 'referencing view' for this digest item.
	pub fn dref(&self) -> DigestItemRef<Hash> {
		match *self {
			Self::ChangesTrieRoot(ref v) => DigestItemRef::ChangesTrieRoot(v),
			Self::PreRuntime(ref v, ref s) => DigestItemRef::PreRuntime(v, s),
			Self::Consensus(ref v, ref s) => DigestItemRef::Consensus(v, s),
			Self::Seal(ref v, ref s) => DigestItemRef::Seal(v, s),
			Self::ChangesTrieSignal(ref s) => DigestItemRef::ChangesTrieSignal(s),
			Self::Other(ref v) => DigestItemRef::Other(v),
			Self::RuntimeEnvironmentUpdated => DigestItemRef::RuntimeEnvironmentUpdated,
		}
	}

	/// Returns `Some` if the entry is the `ChangesTrieRoot` entry.
	pub fn as_changes_trie_root(&self) -> Option<&Hash> {
		self.dref().as_changes_trie_root()
	}

	/// Returns `Some` if this entry is the `PreRuntime` entry.
	pub fn as_pre_runtime(&self) -> Option<(ConsensusEngineId, &[u8])> {
		self.dref().as_pre_runtime()
	}

	/// Returns `Some` if this entry is the `Consensus` entry.
	pub fn as_consensus(&self) -> Option<(ConsensusEngineId, &[u8])> {
		self.dref().as_consensus()
	}

	/// Returns `Some` if this entry is the `Seal` entry.
	pub fn as_seal(&self) -> Option<(ConsensusEngineId, &[u8])> {
		self.dref().as_seal()
	}

	/// Returns `Some` if the entry is the `ChangesTrieSignal` entry.
	pub fn as_changes_trie_signal(&self) -> Option<&ChangesTrieSignal> {
		self.dref().as_changes_trie_signal()
	}

	/// Returns Some if `self` is a `DigestItem::Other`.
	pub fn as_other(&self) -> Option<&[u8]> {
		self.dref().as_other()
	}

	/// Returns the opaque data contained in the item if `Some` if this entry has the id given.
	pub fn try_as_raw(&self, id: OpaqueDigestItemId) -> Option<&[u8]> {
		self.dref().try_as_raw(id)
	}

	/// Returns the data contained in the item if `Some` if this entry has the id given, decoded
	/// to the type provided `T`.
	pub fn try_to<T: Decode>(&self, id: OpaqueDigestItemId) -> Option<T> {
		self.dref().try_to::<T>(id)
	}

	/// Try to match this to a `Self::Seal`, check `id` matches and decode it.
	///
	/// Returns `None` if this isn't a seal item, the `id` doesn't match or when the decoding fails.
	pub fn seal_try_to<T: Decode>(&self, id: &ConsensusEngineId) -> Option<T> {
		self.dref().seal_try_to(id)
	}

	/// Try to match this to a `Self::Consensus`, check `id` matches and decode it.
	///
	/// Returns `None` if this isn't a consensus item, the `id` doesn't match or
	/// when the decoding fails.
	pub fn consensus_try_to<T: Decode>(&self, id: &ConsensusEngineId) -> Option<T> {
		self.dref().consensus_try_to(id)
	}

	/// Try to match this to a `Self::PreRuntime`, check `id` matches and decode it.
	///
	/// Returns `None` if this isn't a pre-runtime item, the `id` doesn't match or
	/// when the decoding fails.
	pub fn pre_runtime_try_to<T: Decode>(&self, id: &ConsensusEngineId) -> Option<T> {
		self.dref().pre_runtime_try_to(id)
	}
}

impl<Hash: Encode> Encode for DigestItem<Hash> {
	fn encode(&self) -> Vec<u8> {
		self.dref().encode()
	}
}

impl<Hash: Encode> codec::EncodeLike for DigestItem<Hash> {}

impl<Hash: Decode> Decode for DigestItem<Hash> {
	#[allow(deprecated)]
	fn decode<I: Input>(input: &mut I) -> Result<Self, Error> {
		let item_type: DigestItemType = Decode::decode(input)?;
		match item_type {
			DigestItemType::ChangesTrieRoot => Ok(Self::ChangesTrieRoot(Decode::decode(input)?)),
			DigestItemType::PreRuntime => {
				let vals: (ConsensusEngineId, Vec<u8>) = Decode::decode(input)?;
				Ok(Self::PreRuntime(vals.0, vals.1))
			},
			DigestItemType::Consensus => {
				let vals: (ConsensusEngineId, Vec<u8>) = Decode::decode(input)?;
				Ok(Self::Consensus(vals.0, vals.1))
			},
			DigestItemType::Seal => {
				let vals: (ConsensusEngineId, Vec<u8>) = Decode::decode(input)?;
				Ok(Self::Seal(vals.0, vals.1))
			},
			DigestItemType::ChangesTrieSignal =>
				Ok(Self::ChangesTrieSignal(Decode::decode(input)?)),
			DigestItemType::Other => Ok(Self::Other(Decode::decode(input)?)),
			DigestItemType::RuntimeEnvironmentUpdated => Ok(Self::RuntimeEnvironmentUpdated),
		}
	}
}

impl<'a, Hash> DigestItemRef<'a, Hash> {
	/// Cast this digest item into `ChangesTrieRoot`.
	pub fn as_changes_trie_root(&self) -> Option<&'a Hash> {
		match *self {
			Self::ChangesTrieRoot(ref changes_trie_root) => Some(changes_trie_root),
			_ => None,
		}
	}

	/// Cast this digest item into `PreRuntime`
	pub fn as_pre_runtime(&self) -> Option<(ConsensusEngineId, &'a [u8])> {
		match *self {
			Self::PreRuntime(consensus_engine_id, ref data) => Some((*consensus_engine_id, data)),
			_ => None,
		}
	}

	/// Cast this digest item into `Consensus`
	pub fn as_consensus(&self) -> Option<(ConsensusEngineId, &'a [u8])> {
		match *self {
			Self::Consensus(consensus_engine_id, ref data) => Some((*consensus_engine_id, data)),
			_ => None,
		}
	}

	/// Cast this digest item into `Seal`
	pub fn as_seal(&self) -> Option<(ConsensusEngineId, &'a [u8])> {
		match *self {
			Self::Seal(consensus_engine_id, ref data) => Some((*consensus_engine_id, data)),
			_ => None,
		}
	}

	/// Cast this digest item into `ChangesTrieSignal`.
	pub fn as_changes_trie_signal(&self) -> Option<&'a ChangesTrieSignal> {
		match *self {
			Self::ChangesTrieSignal(ref changes_trie_signal) => Some(changes_trie_signal),
			_ => None,
		}
	}

	/// Cast this digest item into `PreRuntime`
	pub fn as_other(&self) -> Option<&'a [u8]> {
		match *self {
			Self::Other(ref data) => Some(data),
			_ => None,
		}
	}

	/// Try to match this digest item to the given opaque item identifier; if it matches, then
	/// return the opaque data it contains.
	pub fn try_as_raw(&self, id: OpaqueDigestItemId) -> Option<&'a [u8]> {
		match (id, self) {
			(OpaqueDigestItemId::Consensus(w), &Self::Consensus(v, s)) |
			(OpaqueDigestItemId::Seal(w), &Self::Seal(v, s)) |
			(OpaqueDigestItemId::PreRuntime(w), &Self::PreRuntime(v, s))
				if v == w =>
				Some(&s[..]),
			(OpaqueDigestItemId::Other, &Self::Other(s)) => Some(&s[..]),
			_ => None,
		}
	}

	/// Try to match this digest item to the given opaque item identifier; if it matches, then
	/// try to cast to the given data type; if that works, return it.
	pub fn try_to<T: Decode>(&self, id: OpaqueDigestItemId) -> Option<T> {
		self.try_as_raw(id).and_then(|mut x| Decode::decode(&mut x).ok())
	}

	/// Try to match this to a `Self::Seal`, check `id` matches and decode it.
	///
	/// Returns `None` if this isn't a seal item, the `id` doesn't match or when the decoding fails.
	pub fn seal_try_to<T: Decode>(&self, id: &ConsensusEngineId) -> Option<T> {
		match self {
			Self::Seal(v, s) if *v == id => Decode::decode(&mut &s[..]).ok(),
			_ => None,
		}
	}

	/// Try to match this to a `Self::Consensus`, check `id` matches and decode it.
	///
	/// Returns `None` if this isn't a consensus item, the `id` doesn't match or
	/// when the decoding fails.
	pub fn consensus_try_to<T: Decode>(&self, id: &ConsensusEngineId) -> Option<T> {
		match self {
			Self::Consensus(v, s) if *v == id => Decode::decode(&mut &s[..]).ok(),
			_ => None,
		}
	}

	/// Try to match this to a `Self::PreRuntime`, check `id` matches and decode it.
	///
	/// Returns `None` if this isn't a pre-runtime item, the `id` doesn't match or
	/// when the decoding fails.
	pub fn pre_runtime_try_to<T: Decode>(&self, id: &ConsensusEngineId) -> Option<T> {
		match self {
			Self::PreRuntime(v, s) if *v == id => Decode::decode(&mut &s[..]).ok(),
			_ => None,
		}
	}
}

impl<'a, Hash: Encode> Encode for DigestItemRef<'a, Hash> {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		match *self {
			Self::ChangesTrieRoot(changes_trie_root) => {
				DigestItemType::ChangesTrieRoot.encode_to(&mut v);
				changes_trie_root.encode_to(&mut v);
			},
			Self::Consensus(val, data) => {
				DigestItemType::Consensus.encode_to(&mut v);
				(val, data).encode_to(&mut v);
			},
			Self::Seal(val, sig) => {
				DigestItemType::Seal.encode_to(&mut v);
				(val, sig).encode_to(&mut v);
			},
			Self::PreRuntime(val, data) => {
				DigestItemType::PreRuntime.encode_to(&mut v);
				(val, data).encode_to(&mut v);
			},
			Self::ChangesTrieSignal(changes_trie_signal) => {
				DigestItemType::ChangesTrieSignal.encode_to(&mut v);
				changes_trie_signal.encode_to(&mut v);
			},
			Self::Other(val) => {
				DigestItemType::Other.encode_to(&mut v);
				val.encode_to(&mut v);
			},
			Self::RuntimeEnvironmentUpdated => {
				DigestItemType::RuntimeEnvironmentUpdated.encode_to(&mut v);
			},
		}

		v
	}
}

impl ChangesTrieSignal {
	/// Try to cast this signal to NewConfiguration.
	pub fn as_new_configuration(&self) -> Option<&Option<ChangesTrieConfiguration>> {
		match self {
			Self::NewConfiguration(config) => Some(config),
		}
	}
}

impl<'a, Hash: Encode> codec::EncodeLike for DigestItemRef<'a, Hash> {}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn should_serialize_digest() {
		let digest = Digest {
			logs: vec![
				DigestItem::ChangesTrieRoot(4),
				DigestItem::Other(vec![1, 2, 3]),
				DigestItem::Seal(*b"test", vec![1, 2, 3]),
			],
		};

		assert_eq!(
			serde_json::to_string(&digest).unwrap(),
			r#"{"logs":["0x0204000000","0x000c010203","0x05746573740c010203"]}"#
		);
	}

	#[test]
	fn digest_item_type_info() {
		let type_info = DigestItem::<u32>::type_info();
		let variants = if let scale_info::TypeDef::Variant(variant) = type_info.type_def() {
			variant.variants()
		} else {
			panic!("Should be a TypeDef::TypeDefVariant")
		};

		// ensure that all variants are covered by manual TypeInfo impl
		let check = |digest_item_type: DigestItemType| {
			let (variant_name, digest_item) = match digest_item_type {
				DigestItemType::Other => ("Other", DigestItem::<u32>::Other(Default::default())),
				DigestItemType::ChangesTrieRoot =>
					("ChangesTrieRoot", DigestItem::ChangesTrieRoot(Default::default())),
				DigestItemType::Consensus =>
					("Consensus", DigestItem::Consensus(Default::default(), Default::default())),
				DigestItemType::Seal =>
					("Seal", DigestItem::Seal(Default::default(), Default::default())),
				DigestItemType::PreRuntime =>
					("PreRuntime", DigestItem::PreRuntime(Default::default(), Default::default())),
				DigestItemType::ChangesTrieSignal => (
					"ChangesTrieSignal",
					DigestItem::ChangesTrieSignal(ChangesTrieSignal::NewConfiguration(
						Default::default(),
					)),
				),
				DigestItemType::RuntimeEnvironmentUpdated =>
					("RuntimeEnvironmentUpdated", DigestItem::RuntimeEnvironmentUpdated),
			};
			let encoded = digest_item.encode();
			let variant = variants
				.iter()
				.find(|v| v.name() == &variant_name)
				.expect(&format!("Variant {} not found", variant_name));

			assert_eq!(encoded[0], variant.index())
		};

		check(DigestItemType::Other);
		check(DigestItemType::ChangesTrieRoot);
		check(DigestItemType::Consensus);
		check(DigestItemType::Seal);
		check(DigestItemType::PreRuntime);
		check(DigestItemType::ChangesTrieSignal);
		check(DigestItemType::RuntimeEnvironmentUpdated);
	}
}
