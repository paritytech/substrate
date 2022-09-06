// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{traits::ConstU32, BoundedVec};
use scale_info::TypeInfo;
use sp_runtime::RuntimeDebug;
use sp_std::{convert::TryInto, prelude::*};

/// A Multihash instance that only supports the basic functionality and no hashing.
#[derive(
	Clone, PartialEq, Eq, PartialOrd, Ord, RuntimeDebug, Encode, Decode, TypeInfo, MaxEncodedLen,
)]
pub struct Multihash {
	/// The code of the Multihash.
	pub code: u64,
	/// The digest.
	pub digest: BoundedVec<u8, ConstU32<68>>, // 4 byte dig size + 64 bytes hash digest
}

impl Multihash {
	/// Returns the size of the digest.
	pub fn size(&self) -> usize {
		self.digest.len()
	}
}

/// The version of the CID.
#[derive(
	Clone,
	Copy,
	PartialEq,
	Eq,
	PartialOrd,
	Ord,
	RuntimeDebug,
	Encode,
	Decode,
	TypeInfo,
	MaxEncodedLen,
)]
pub enum Version {
	/// CID version 0.
	V0,
	/// CID version 1.
	V1,
}

/// Representation of a CID.
///
/// The generic is about the allocated size of the multihash.
#[derive(
	Clone, PartialEq, Eq, PartialOrd, Ord, RuntimeDebug, Encode, Decode, TypeInfo, MaxEncodedLen,
)]
pub struct Cid {
	/// The version of CID.
	pub version: Version,
	/// The codec of CID.
	pub codec: u64,
	/// The multihash of CID.
	pub hash: Multihash,
}

impl Cid {
	/// Creates a new CIDv0.
	pub fn new_v0(sha2_256_digest: impl Into<Vec<u8>>) -> Self {
		/// DAG-PB multicodec code
		const DAG_PB: u64 = 0x70;
		/// The SHA_256 multicodec code
		const SHA2_256: u64 = 0x12;

		let digest = sha2_256_digest.into();
		assert_eq!(digest.len(), 32);

		Self {
			version: Version::V0,
			codec: DAG_PB,
			hash: Multihash { code: SHA2_256, digest: digest.try_into().expect("msg") },
		}
	}
}

/// Witness data for the `disband` call.
#[derive(
	Copy, Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, MaxEncodedLen, TypeInfo, Default,
)]
pub struct DisbandWitness {
	/// Total number of voting members in the current Alliance.
	#[codec(compact)]
	pub(super) voting_members: u32,
	/// Total number of ally members in the current Alliance.
	#[codec(compact)]
	pub(super) ally_members: u32,
}

#[cfg(test)]
impl DisbandWitness {
	// Creates new DisbandWitness.
	pub(super) fn new(voting_members: u32, ally_members: u32) -> Self {
		Self { voting_members, ally_members }
	}
}

impl DisbandWitness {
	pub(super) fn is_zero(self) -> bool {
		self == Self::default()
	}
}
