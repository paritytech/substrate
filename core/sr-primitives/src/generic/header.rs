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
	Hash as HashT, DigestItem as DigestItemT};
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

// Hack to work around the fact that deriving deserialize doesn't work nicely with
// the `hashing` trait used as a parameter.
// dummy struct that uses the hash type directly.
// https://github.com/serde-rs/serde/issues/1296
#[cfg(feature = "std")]
#[serde(rename_all = "camelCase")]
#[derive(Deserialize)]
struct DeserializeHeader<N, H, D> {
	parent_hash: H,
	number: N,
	state_root: H,
	extrinsics_root: H,
	digest: Digest<D>,
}

#[cfg(feature = "std")]
impl<N, D, Hash: HashT> From<DeserializeHeader<N, Hash::Output, D>> for Header<N, Hash, D> {
	fn from(other: DeserializeHeader<N, Hash::Output, D>) -> Self {
		Header {
			parent_hash: other.parent_hash,
			number: other.number,
			state_root: other.state_root,
			extrinsics_root: other.extrinsics_root,
			digest: other.digest,
		}
	}
}

#[cfg(feature = "std")]
impl<'a, Number: 'a, Hash: 'a + HashT, DigestItem: 'a> Deserialize<'a> for Header<Number, Hash, DigestItem> where
	Number: Deserialize<'a>,
	Hash::Output: Deserialize<'a>,
	DigestItem: Deserialize<'a>,
{
	fn deserialize<D: Deserializer<'a>>(de: D) -> Result<Self, D::Error> {
		DeserializeHeader::<Number, Hash::Output, DigestItem>::deserialize(de).map(Into::into)
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

impl<Number, Hash, DigestItem> traits::Header for Header<Number, Hash, DigestItem> where
	Number: Member + ::rstd::hash::Hash + Copy + MaybeDisplay + SimpleArithmetic + Codec,
	Hash: HashT,
	DigestItem: DigestItemT<Hash = Hash::Output> + Codec,
	Hash::Output: Default + ::rstd::hash::Hash + Copy + Member + MaybeDisplay + SimpleBitOps + Codec,
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
