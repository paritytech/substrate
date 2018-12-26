// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Generic implementation of a block header.

#[cfg(feature = "std")]
use serde::{Deserialize, Deserializer};

use codec::{Decode, Encode, Codec, Input, Output, HasCompact};
use traits::{self, Member, SimpleArithmetic, SimpleBitOps, MaybeDisplay,
	Hash as HashT, DigestItem as DigestItemT, MaybeSerializeDebug, MaybeSerializeDebugButNotDeserialize};
use generic::Digest;

/// Abstraction over a block header for a substrate chain.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct Header<Number, Hash: HashT, DigestItem> {
	/// The parent hash.
	pub parent_hash: <Hash as HashT>::Output,
	/// The block number.
	pub number: Number,
	/// The state trie merkle root
	pub state_root: <Hash as HashT>::Output,
	/// The merkle root of the extrinsics.
	pub extrinsics_root: <Hash as HashT>::Output,
	/// A chain-specific digest of data useful for light clients or referencing auxiliary data.
	pub digest: Digest<DigestItem>,
}

// TODO: Remove Deserialize for Header once RPC no longer needs it #1098
#[cfg(feature = "std")]
impl<'a, Number: 'a, Hash: 'a + HashT, DigestItem: 'a> Deserialize<'a> for Header<Number, Hash, DigestItem> where
	Header<Number, Hash, DigestItem>: Decode,
{
	fn deserialize<D: Deserializer<'a>>(de: D) -> Result<Self, D::Error> {
		let r = <Vec<u8>>::deserialize(de)?;
		Decode::decode(&mut &r[..]).ok_or(::serde::de::Error::custom("Invalid value passed into decode"))
	}
}

impl<Number, Hash, DigestItem> Decode for Header<Number, Hash, DigestItem> where
	Number: HasCompact,
	Hash: HashT,
	Hash::Output: Decode,
	DigestItem: DigestItemT + Decode,
{
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(Header {
			parent_hash: Decode::decode(input)?,
			number: <<Number as HasCompact>::Type>::decode(input)?.into(),
			state_root: Decode::decode(input)?,
			extrinsics_root: Decode::decode(input)?,
			digest: Decode::decode(input)?,
		})
	}
}

impl<Number, Hash, DigestItem> Encode for Header<Number, Hash, DigestItem> where
	Number: HasCompact + Copy,
	Hash: HashT,
	Hash::Output: Encode,
	DigestItem: DigestItemT + Encode,
{
	fn encode_to<T: Output>(&self, dest: &mut T) {
		dest.push(&self.parent_hash);
		dest.push(&<<Number as HasCompact>::Type>::from(self.number));
		dest.push(&self.state_root);
		dest.push(&self.extrinsics_root);
		dest.push(&self.digest);
	}
}

impl<Number, Hash, DigestItem> substrate_metadata::EncodeMetadata for Header<Number, Hash, DigestItem> where
	Number: HasCompact + Copy,
	Hash: HashT,
	Hash::Output: Encode,
	DigestItem: DigestItemT + Encode,
{
	fn type_metadata() -> substrate_metadata::Metadata {
		// TODO: implement this
		substrate_metadata::Metadata {
			kind: substrate_metadata::TypeMetadata::Primative(substrate_metadata::PrimativeMetadata::Unknown)
		}
	}
}

impl<Number, Hash, DigestItem> traits::Header for Header<Number, Hash, DigestItem> where
	Number: Member + MaybeSerializeDebug + ::rstd::hash::Hash + Copy + MaybeDisplay + SimpleArithmetic + Codec,
	Hash: HashT,
	DigestItem: DigestItemT<Hash = Hash::Output> + Codec,
	Hash::Output: Default + ::rstd::hash::Hash + Copy + Member + MaybeSerializeDebugButNotDeserialize + MaybeDisplay + SimpleBitOps + Codec,
{
	type Number = Number;
	type Hash = <Hash as HashT>::Output;
	type Hashing = Hash;
	type Digest = Digest<DigestItem>;

	fn number(&self) -> &Self::Number { &self.number }
	fn set_number(&mut self, num: Self::Number) { self.number = num }

	fn extrinsics_root(&self) -> &Self::Hash { &self.extrinsics_root }
	fn set_extrinsics_root(&mut self, root: Self::Hash) { self.extrinsics_root = root }

	fn state_root(&self) -> &Self::Hash { &self.state_root }
	fn set_state_root(&mut self, root: Self::Hash) { self.state_root = root }

	fn parent_hash(&self) -> &Self::Hash { &self.parent_hash }
	fn set_parent_hash(&mut self, hash: Self::Hash) { self.parent_hash = hash }

	fn digest(&self) -> &Self::Digest { &self.digest }
	fn digest_mut(&mut self) -> &mut Self::Digest { &mut self.digest }
	fn set_digest(&mut self, digest: Self::Digest) { self.digest = digest }

	fn new(
		number: Self::Number,
		extrinsics_root: Self::Hash,
		state_root: Self::Hash,
		parent_hash: Self::Hash,
		digest: Self::Digest
	) -> Self {
		Header {
			number,
			extrinsics_root,
			state_root,
			parent_hash,
			digest
		}
	}
}

impl<Number, Hash, DigestItem> Header<Number, Hash, DigestItem> where
	Number: Member + ::rstd::hash::Hash + Copy + MaybeDisplay + SimpleArithmetic + Codec,
	Hash: HashT,
	DigestItem: DigestItemT + Codec,
	Hash::Output: Default + ::rstd::hash::Hash + Copy + Member + MaybeDisplay + SimpleBitOps + Codec,
 {
	/// Convenience helper for computing the hash of the header without having
	/// to import the trait.
	pub fn hash(&self) -> Hash::Output {
		Hash::hash_of(self)
	}
}
