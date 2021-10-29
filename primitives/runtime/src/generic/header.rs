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

//! Generic implementation of a block header.

use crate::{
	codec::{Codec, Decode, Encode},
	generic::Digest,
	scale_info::TypeInfo,
	traits::{
		self, AtLeast32BitUnsigned, Hash as HashT, MaybeDisplay, MaybeMallocSizeOf, MaybeSerialize,
		MaybeSerializeDeserialize, Member, SimpleBitOps,
	},
};
#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};
use sp_core::U256;
use sp_std::{convert::TryFrom, fmt::Debug};

/// Abstraction over a block header for a substrate chain.
#[derive(Encode, Decode, PartialEq, Eq, Clone, sp_core::RuntimeDebug, TypeInfo)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct Header<Number: Copy + Into<U256> + TryFrom<U256>, Hash: HashT> {
	/// The parent hash.
	pub parent_hash: Hash::Output,
	/// The block number.
	#[cfg_attr(
		feature = "std",
		serde(serialize_with = "serialize_number", deserialize_with = "deserialize_number")
	)]
	#[codec(compact)]
	pub number: Number,
	/// The state trie merkle root
	pub state_root: Hash::Output,
	/// The merkle root of the extrinsics.
	pub extrinsics_root: Hash::Output,
	/// A chain-specific digest of data useful for light clients or referencing auxiliary data.
	pub digest: Digest<Hash::Output>,
}

#[cfg(feature = "std")]
impl<Number, Hash> parity_util_mem::MallocSizeOf for Header<Number, Hash>
where
	Number: Copy + Into<U256> + TryFrom<U256> + parity_util_mem::MallocSizeOf,
	Hash: HashT,
	Hash::Output: parity_util_mem::MallocSizeOf,
{
	fn size_of(&self, ops: &mut parity_util_mem::MallocSizeOfOps) -> usize {
		self.parent_hash.size_of(ops) +
			self.number.size_of(ops) +
			self.state_root.size_of(ops) +
			self.extrinsics_root.size_of(ops) +
			self.digest.size_of(ops)
	}
}

#[cfg(feature = "std")]
pub fn serialize_number<S, T: Copy + Into<U256> + TryFrom<U256>>(
	val: &T,
	s: S,
) -> Result<S::Ok, S::Error>
where
	S: serde::Serializer,
{
	let u256: U256 = (*val).into();
	serde::Serialize::serialize(&u256, s)
}

#[cfg(feature = "std")]
pub fn deserialize_number<'a, D, T: Copy + Into<U256> + TryFrom<U256>>(d: D) -> Result<T, D::Error>
where
	D: serde::Deserializer<'a>,
{
	let u256: U256 = serde::Deserialize::deserialize(d)?;
	TryFrom::try_from(u256).map_err(|_| serde::de::Error::custom("Try from failed"))
}

impl<Number, Hash> traits::Header for Header<Number, Hash>
where
	Number: Member
		+ MaybeSerializeDeserialize
		+ Debug
		+ sp_std::hash::Hash
		+ MaybeDisplay
		+ AtLeast32BitUnsigned
		+ Codec
		+ Copy
		+ Into<U256>
		+ TryFrom<U256>
		+ sp_std::str::FromStr
		+ MaybeMallocSizeOf,
	Hash: HashT,
	Hash::Output: Default
		+ sp_std::hash::Hash
		+ Copy
		+ Member
		+ Ord
		+ MaybeSerialize
		+ Debug
		+ MaybeDisplay
		+ SimpleBitOps
		+ Codec
		+ MaybeMallocSizeOf,
{
	type Number = Number;
	type Hash = <Hash as HashT>::Output;
	type Hashing = Hash;

	fn number(&self) -> &Self::Number {
		&self.number
	}
	fn set_number(&mut self, num: Self::Number) {
		self.number = num
	}

	fn extrinsics_root(&self) -> &Self::Hash {
		&self.extrinsics_root
	}
	fn set_extrinsics_root(&mut self, root: Self::Hash) {
		self.extrinsics_root = root
	}

	fn state_root(&self) -> &Self::Hash {
		&self.state_root
	}
	fn set_state_root(&mut self, root: Self::Hash) {
		self.state_root = root
	}

	fn parent_hash(&self) -> &Self::Hash {
		&self.parent_hash
	}
	fn set_parent_hash(&mut self, hash: Self::Hash) {
		self.parent_hash = hash
	}

	fn digest(&self) -> &Digest<Self::Hash> {
		&self.digest
	}

	fn digest_mut(&mut self) -> &mut Digest<Self::Hash> {
		#[cfg(feature = "std")]
		log::debug!(target: "header", "Retrieving mutable reference to digest");
		&mut self.digest
	}

	fn new(
		number: Self::Number,
		extrinsics_root: Self::Hash,
		state_root: Self::Hash,
		parent_hash: Self::Hash,
		digest: Digest<Self::Hash>,
	) -> Self {
		Self { number, extrinsics_root, state_root, parent_hash, digest }
	}
}

impl<Number, Hash> Header<Number, Hash>
where
	Number: Member
		+ sp_std::hash::Hash
		+ Copy
		+ MaybeDisplay
		+ AtLeast32BitUnsigned
		+ Codec
		+ Into<U256>
		+ TryFrom<U256>,
	Hash: HashT,
	Hash::Output:
		Default + sp_std::hash::Hash + Copy + Member + MaybeDisplay + SimpleBitOps + Codec,
{
	/// Convenience helper for computing the hash of the header without having
	/// to import the trait.
	pub fn hash(&self) -> Hash::Output {
		Hash::hash_of(self)
	}
}

#[cfg(all(test, feature = "std"))]
mod tests {
	use super::*;
	use crate::traits::BlakeTwo256;

	#[test]
	fn should_serialize_numbers() {
		fn serialize(num: u128) -> String {
			let mut v = vec![];
			{
				let mut ser = serde_json::Serializer::new(std::io::Cursor::new(&mut v));
				serialize_number(&num, &mut ser).unwrap();
			}
			String::from_utf8(v).unwrap()
		}

		assert_eq!(serialize(0), "\"0x0\"".to_owned());
		assert_eq!(serialize(1), "\"0x1\"".to_owned());
		assert_eq!(serialize(u64::MAX as u128), "\"0xffffffffffffffff\"".to_owned());
		assert_eq!(serialize(u64::MAX as u128 + 1), "\"0x10000000000000000\"".to_owned());
	}

	#[test]
	fn should_deserialize_number() {
		fn deserialize(num: &str) -> u128 {
			let mut der = serde_json::Deserializer::new(serde_json::de::StrRead::new(num));
			deserialize_number(&mut der).unwrap()
		}

		assert_eq!(deserialize("\"0x0\""), 0);
		assert_eq!(deserialize("\"0x1\""), 1);
		assert_eq!(deserialize("\"0xffffffffffffffff\""), u64::MAX as u128);
		assert_eq!(deserialize("\"0x10000000000000000\""), u64::MAX as u128 + 1);
	}

	#[test]
	fn ensure_format_is_unchanged() {
		let header = Header::<u32, BlakeTwo256> {
			parent_hash: BlakeTwo256::hash(b"1"),
			number: 2,
			state_root: BlakeTwo256::hash(b"3"),
			extrinsics_root: BlakeTwo256::hash(b"4"),
			digest: crate::generic::Digest {
				logs: vec![
					crate::generic::DigestItem::ChangesTrieRoot(BlakeTwo256::hash(b"5")),
					crate::generic::DigestItem::Other(b"6".to_vec()),
				],
			},
		};

		let header_encoded = header.encode();
		assert_eq!(
			header_encoded,
			vec![
				146, 205, 245, 120, 196, 112, 133, 165, 153, 34, 86, 240, 220, 249, 125, 11, 25,
				241, 241, 201, 222, 77, 95, 227, 12, 58, 206, 97, 145, 182, 229, 219, 8, 88, 19,
				72, 51, 123, 15, 62, 20, 134, 32, 23, 61, 170, 165, 249, 77, 0, 216, 129, 112, 93,
				203, 240, 170, 131, 239, 218, 186, 97, 210, 237, 225, 235, 134, 73, 33, 73, 151,
				87, 78, 32, 196, 100, 56, 138, 23, 36, 32, 210, 84, 3, 104, 43, 187, 184, 12, 73,
				104, 49, 200, 204, 31, 143, 13, 8, 2, 112, 178, 1, 53, 47, 36, 191, 28, 151, 112,
				185, 159, 143, 113, 32, 24, 33, 65, 28, 244, 20, 55, 124, 155, 140, 45, 188, 238,
				97, 219, 135, 214, 0, 4, 54
			],
		);
		assert_eq!(header, Header::<u32, BlakeTwo256>::decode(&mut &header_encoded[..]).unwrap());

		let header = Header::<u32, BlakeTwo256> {
			parent_hash: BlakeTwo256::hash(b"1000"),
			number: 2000,
			state_root: BlakeTwo256::hash(b"3000"),
			extrinsics_root: BlakeTwo256::hash(b"4000"),
			digest: crate::generic::Digest {
				logs: vec![
					crate::generic::DigestItem::Other(b"5000".to_vec()),
					crate::generic::DigestItem::ChangesTrieRoot(BlakeTwo256::hash(b"6000")),
				],
			},
		};

		let header_encoded = header.encode();
		assert_eq!(
			header_encoded,
			vec![
				197, 243, 254, 225, 31, 117, 21, 218, 179, 213, 92, 6, 247, 164, 230, 25, 47, 166,
				140, 117, 142, 159, 195, 202, 67, 196, 238, 26, 44, 18, 33, 92, 65, 31, 219, 225,
				47, 12, 107, 88, 153, 146, 55, 21, 226, 186, 110, 48, 167, 187, 67, 183, 228, 232,
				118, 136, 30, 254, 11, 87, 48, 112, 7, 97, 31, 82, 146, 110, 96, 87, 152, 68, 98,
				162, 227, 222, 78, 14, 244, 194, 120, 154, 112, 97, 222, 144, 174, 101, 220, 44,
				111, 126, 54, 34, 155, 220, 253, 124, 8, 0, 16, 53, 48, 48, 48, 2, 42, 105, 109,
				150, 206, 223, 24, 44, 164, 77, 27, 137, 177, 220, 25, 170, 140, 35, 156, 246, 233,
				112, 26, 23, 192, 61, 226, 14, 84, 219, 144, 252
			],
		);
		assert_eq!(header, Header::<u32, BlakeTwo256>::decode(&mut &header_encoded[..]).unwrap());
	}
}
