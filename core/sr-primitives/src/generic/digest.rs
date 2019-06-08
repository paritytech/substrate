// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Generic implementation of a digest.

#[cfg(feature = "std")]
use serde::Serialize;

use rstd::prelude::*;

use crate::ConsensusEngineId;
use crate::codec::{Decode, Encode, Codec, Input};
use crate::traits::{self, Member, DigestItem as DigestItemT, MaybeHash};

/// Generic header digest.
#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
pub struct Digest<Item> {
	/// A list of logs in the digest.
	pub logs: Vec<Item>,
}

impl<Item> Default for Digest<Item> {
	fn default() -> Self {
		Digest { logs: Vec::new(), }
	}
}

impl<Item> traits::Digest for Digest<Item> where
	Item: DigestItemT + Codec
{
	type Hash = Item::Hash;
	type Item = Item;

	fn logs(&self) -> &[Self::Item] {
		&self.logs
	}

	fn push(&mut self, item: Self::Item) {
		self.logs.push(item);
	}

	fn pop(&mut self) -> Option<Self::Item> {
		self.logs.pop()
	}
}

// Macro black magic.
macro_rules! gen_digest_type {
	(
		$( #[doc = $main_docs:tt] )*
		pub enum $main:ident $(<$($main_params: tt),+>)? { }
		$(
			$( #[doc = $doc_attr:tt] )*
			pub enum $n:ident $(<$($t: tt),+>)? {
				$(
					$( #[doc = $variant_doc:tt] )*
					$variant:ident(($($interior: ty),*), $q: tt),
				)*
			}
		)+
	) => {
		$( #[doc = $main_docs] )*
		#[derive(PartialEq, Eq, Clone)]
		#[cfg_attr(feature = "std", derive(Debug))]
		pub enum $main $(<$($main_params),+>)? {
			$(
				$(
					$( #[doc = $variant_doc] )*
					$variant($($interior),*),
				)*
			)*
		}

		gen_digest_type! {
			@internal
			$main : $main $(<$($main_params),+>)? => $(
				$( #[doc = $doc_attr] )*
				pub enum $n $(<$($t),+>)? {
					$(
						$( #[doc = $variant_doc] )*
						$variant(($($interior),*), $q),
					)*
				}
			)+
		}
	};
	(
		@internal
		$main_id:tt : $main:ty => $(
			$( #[doc = $doc_attr:tt] )*
			pub enum $n:ident $(<$($t: tt),+>)? {
				$(
					$( #[doc = $variant_doc:tt] )*
					$variant:ident(($($interior: ty),*), $q: tt),
				)*
			}
		)+
	) => {
		$(
			$( #[doc = $doc_attr] )*
			#[derive(PartialEq, Eq, Clone)]
			#[cfg_attr(feature = "std", derive(Debug))]
			pub enum $n $(<$($t),+>)? {
				$(
					$( #[doc = $variant_doc] )*
					$variant($($interior),*),
				)*
			}

			impl<Hash, AuthorityId, SealSignature> From<$n $(<$($t),*>)?>
				for $main {
				fn from(digest: $n $(<$($t),+>)?) -> Self {
					match digest {
						$(
							$n::$variant $q => $main_id::$variant $q,
						)*
					}
				}
			}
		)*
	};
}

gen_digest_type! {
	/// Digest item that is able to encode/decode 'system' digest items and
	/// provide opaque access to other items.
	///
	/// For all variants that include a `ConsensusEngineId`, consensus engine
	/// implementations **MUST** ignore digests that have a `ConsensusEngineId`
	/// that is not theirs.  Node implementations **MUST** reject digests that
	/// have a `ConsensusEngineId` that corresponds to a consensus engine not in
	/// use.  Node implementations **MUST** reject blocks as malformed if they
	/// reject any of the block’s digest.  If the runtime supports this, the
	/// node that issued the block **SHOULD** be reported as having committed
	/// severe misbehavior and punished accordingly.  The invalid block, or its
	/// hash, **SHOULD** constitute adequate proof of such misbehavior.
	pub enum DigestItem<Hash, AuthorityId, SealSignature> {}

	/// A digest item that can be produced by consensus engines. Consensus
	/// engine implementations **MUST NOT** push digests not in this variant.
	/// This **SHOULD** be detected at compile time. If it is not, the behavior
	/// of the blockchain is undefined.
	pub enum ConsensusDigest<SealSignature> {
		/// Put a Seal on it. This **MUST** come after all other `DigestItem`
		/// variants. There **MUST** be exactly one `Seal` per consensus engine,
		/// and its `ConsensusEngineId` **MUST** be that of the consensus engine
		/// that produced it. Runtimes will not see this variant.
		Seal((ConsensusEngineId, SealSignature), (a, b)),
		/// An inherent digest.
		///
		/// These are messages from the consensus engine to the runtime,
		/// although the consensus engine can (and should) read them itself to
		/// avoid code and state duplication. It is erroneous for a runtime to
		/// produce these, but this is checked at compile time. Runtimes can
		/// (and should) trust these, as with any other inherent. Consensus
		/// engines MUST verify them.
		PreRuntime((ConsensusEngineId, Vec<u8>), (a, b)),
	}

	/// A digest item that can be produced by runtimes. Runtime mplementations
	/// **MUST NOT** push digests not in this variant. This **SHOULD** be
	/// detected at compile time.  If it is not, the behavior of the blockchain
	/// is undefined.
	pub enum RuntimeDigest {
		/// A message from the runtime to the consensus engine. This MUST NOT be
		/// generated by the native code of any consensus engine, but this is
		/// caught at compile time. The `ConsensusEngineId` is that of the
		/// consensus engine for which this digest is intended. Consensus
		/// engines MUST ignore digests with `ConsensusEngineId`s other than
		/// their own.
		Consensus((ConsensusEngineId, Vec<u8>), (a, b)),
		/// Any 'non-system' digest item, opaque to the native code.  Runtimes
		/// MUST verify these, and reject any they did not produce.  These MUST
		/// NOT be produced by native code.
		Other((Vec<u8>), (a)),
	}

	/// A digest item that is reserved for the SRML. Only the SRML is allowed to
	/// push these digests. Consensus engines and third-party runtime code
	/// **MUST NOT** push digests in this variant. This **SHOULD** be detected
	/// at compile time. If it is not, the behavior of the blockchain is
	/// undefined.
	pub enum SystemDigest<Hash, AuthorityId> {
		/// System digest item announcing that authorities set has been changed
		/// in the block. Contains the new set of authorities.
		AuthoritiesChange((Vec<AuthorityId>), (a)),
		/// System digest item that contains the root of changes trie at given
		/// block. It is created for every block iff runtime supports changes
		/// trie creation.
		ChangesTrieRoot((Hash), (a)),
	}
}

#[cfg(feature = "std")]
impl<Hash: Encode, AuthorityId: Encode, SealSignature: Encode> ::serde::Serialize for DigestItem<Hash, AuthorityId, SealSignature> {
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
		self.using_encoded(|bytes| {
			::substrate_primitives::bytes::serialize(bytes, seq)
		})
	}
}


/// A 'referencing view' for digest item. Does not own its contents. Used by
/// final runtime implementations for encoding/decoding its log items.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum DigestItemRef<'a, Hash: 'a, AuthorityId: 'a, SealSignature: 'a> {
	/// Reference to `DigestItem::AuthoritiesChange`.
	AuthoritiesChange(&'a [AuthorityId]),
	/// Reference to `DigestItem::ChangesTrieRoot`.
	ChangesTrieRoot(&'a Hash),
	/// A message from the runtime to the consensus engine. This should *never*
	/// be generated by the native code of any consensus engine, but this is not
	/// checked (yet).
	Consensus(&'a ConsensusEngineId, &'a Vec<u8>),
	/// Put a Seal on it. This is only used by native code, and is never seen
	/// by runtimes.
	Seal(&'a ConsensusEngineId, &'a SealSignature),
	/// A pre-runtime digest.
	///
	/// These are messages from the consensus engine to the runtime, although
	/// the consensus engine can (and should) read them itself to avoid
	/// code and state duplication.  It is erroneous for a runtime to produce
	/// these, but this is not (yet) checked.
	PreRuntime(&'a ConsensusEngineId, &'a Vec<u8>),
	/// Any 'non-system' digest item, opaque to the native code.
	Other(&'a Vec<u8>),
}

/// Type of the digest item. Used to gain explicit control over `DigestItem` encoding
/// process. We need an explicit control, because final runtimes are encoding their own
/// digest items using `DigestItemRef` type and we can't auto-derive `Decode`
/// trait for `DigestItemRef`.
#[repr(u32)]
#[derive(Encode, Decode)]
enum DigestItemType {
	Other = 0,
	AuthoritiesChange = 1,
	ChangesTrieRoot = 2,
	Consensus = 4,
	Seal = 5,
	PreRuntime = 6,
}

impl<Hash, AuthorityId, SealSignature> DigestItem<Hash, AuthorityId, SealSignature> {
	/// Returns Some if `self` is a `DigestItem::Other`.
	pub fn as_other(&self) -> Option<&Vec<u8>> {
		match *self {
			DigestItem::Other(ref v) => Some(v),
			_ => None,
		}
	}

	/// Returns a 'referencing view' for this digest item.
	fn dref<'a>(&'a self) -> DigestItemRef<'a, Hash, AuthorityId, SealSignature> {
		match *self {
			DigestItem::AuthoritiesChange(ref v) => DigestItemRef::AuthoritiesChange(v),
			DigestItem::ChangesTrieRoot(ref v) => DigestItemRef::ChangesTrieRoot(v),
			DigestItem::Consensus(ref v, ref s) => DigestItemRef::Consensus(v, s),
			DigestItem::Seal(ref v, ref s) => DigestItemRef::Seal(v, s),
			DigestItem::PreRuntime(ref v, ref s) => DigestItemRef::PreRuntime(v, s),
			DigestItem::Other(ref v) => DigestItemRef::Other(v),
		}
	}
}

impl<
	Hash: Codec + Member,
	AuthorityId: Codec + Member + MaybeHash,
	SealSignature: Codec + Member,
> traits::DigestItem for DigestItem<Hash, AuthorityId, SealSignature> {
	type Hash = Hash;
	type AuthorityId = AuthorityId;

	fn as_authorities_change(&self) -> Option<&[Self::AuthorityId]> {
		self.dref().as_authorities_change()
	}

	fn as_changes_trie_root(&self) -> Option<&Self::Hash> {
		self.dref().as_changes_trie_root()
	}

	fn as_pre_runtime(&self) -> Option<(ConsensusEngineId, &[u8])> {
		self.dref().as_pre_runtime()
	}
}

impl<Hash: Encode, AuthorityId: Encode, SealSignature: Encode> Encode for DigestItem<Hash, AuthorityId, SealSignature> {
	fn encode(&self) -> Vec<u8> {
		self.dref().encode()
	}
}

impl<Hash: Decode, AuthorityId: Decode, SealSignature: Decode> Decode for DigestItem<Hash, AuthorityId, SealSignature> {
	#[allow(deprecated)]
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		let item_type: DigestItemType = Decode::decode(input)?;
		match item_type {
			DigestItemType::AuthoritiesChange => Some(DigestItem::AuthoritiesChange(
				Decode::decode(input)?,
			)),
			DigestItemType::ChangesTrieRoot => Some(DigestItem::ChangesTrieRoot(
				Decode::decode(input)?,
			)),
			DigestItemType::Consensus => {
				let vals: (ConsensusEngineId, Vec<u8>) = Decode::decode(input)?;
				Some(DigestItem::Consensus(vals.0, vals.1))
			}
			DigestItemType::Seal => {
				let vals: (ConsensusEngineId, SealSignature) = Decode::decode(input)?;
				Some(DigestItem::Seal(vals.0, vals.1))
			},
			DigestItemType::PreRuntime => {
				let vals: (ConsensusEngineId, Vec<u8>) = Decode::decode(input)?;
				Some(DigestItem::PreRuntime(vals.0, vals.1))
			},
			DigestItemType::Other => Some(DigestItem::Other(
				Decode::decode(input)?,
			)),
		}
	}
}

impl<'a, Hash: Codec + Member, AuthorityId: Codec + Member, SealSignature: Codec + Member> DigestItemRef<'a, Hash, AuthorityId, SealSignature> {
	/// Cast this digest item into `AuthoritiesChange`.
	pub fn as_authorities_change(&self) -> Option<&'a [AuthorityId]> {
		match *self {
			DigestItemRef::AuthoritiesChange(ref authorities) => Some(authorities),
			_ => None,
		}
	}

	/// Cast this digest item into `ChangesTrieRoot`.
	pub fn as_changes_trie_root(&self) -> Option<&'a Hash> {
		match *self {
			DigestItemRef::ChangesTrieRoot(ref changes_trie_root) => Some(changes_trie_root),
			_ => None,
		}
	}

	/// Cast this digest item into `PreRuntime`
	pub fn as_pre_runtime(&self) -> Option<(ConsensusEngineId, &'a [u8])> {
		match *self {
			DigestItemRef::PreRuntime(consensus_engine_id, ref data) => Some((*consensus_engine_id, data)),
			_ => None,
		}
	}
}

impl<'a, Hash: Encode, AuthorityId: Encode, SealSignature: Encode> Encode for DigestItemRef<'a, Hash, AuthorityId, SealSignature> {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		match *self {
			DigestItemRef::AuthoritiesChange(authorities) => {
				DigestItemType::AuthoritiesChange.encode_to(&mut v);
				authorities.encode_to(&mut v);
			},
			DigestItemRef::ChangesTrieRoot(changes_trie_root) => {
				DigestItemType::ChangesTrieRoot.encode_to(&mut v);
				changes_trie_root.encode_to(&mut v);
			},
			DigestItemRef::Consensus(val, data) => {
				DigestItemType::Consensus.encode_to(&mut v);
				(val, data).encode_to(&mut v);
			},
			DigestItemRef::Seal(val, sig) => {
				DigestItemType::Seal.encode_to(&mut v);
				(val, sig).encode_to(&mut v);
			},
			DigestItemRef::PreRuntime(val, data) => {
				DigestItemType::PreRuntime.encode_to(&mut v);
				(val, data).encode_to(&mut v);
			},
			DigestItemRef::Other(val) => {
				DigestItemType::Other.encode_to(&mut v);
				val.encode_to(&mut v);
			},
		}

		v
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use substrate_primitives::hash::H512 as Signature;

	#[test]
	fn should_serialize_digest() {
		let digest = Digest {
			logs: vec![
				DigestItem::AuthoritiesChange(vec![1]),
				DigestItem::ChangesTrieRoot(4),
				DigestItem::Other(vec![1, 2, 3]),
				DigestItem::Seal(Default::default(), Signature::default())
			],
		};

		assert_eq!(
			::serde_json::to_string(&digest).unwrap(),
			"{\"logs\":[\"0x010401000000\",\"0x0204000000\",\"0x000c010203\",\"0x050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000\"]}",
		);
	}
}
