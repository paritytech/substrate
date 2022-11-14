// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! BEEFY + MMR utilties.
//!
//! While BEEFY can be used completely indepentently as an additional consensus gadget,
//! it is designed around a main use case of making bridging standalone networks together.
//! For that use case it's common to use some aggregated data structure (like MMR) to be
//! used in conjunction with BEEFY, to be able to efficiently prove any past blockchain data.
//!
//! This module contains primitives used by Polkadot implementation of the BEEFY+MMR bridge,
//! but we imagine they will be useful for other chains that either want to bridge with Polkadot
//! or are completely standalone, but heavily inspired by Polkadot.

use crate::Vec;
use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

/// A provider for extra data that gets added to the Mmr leaf
pub trait BeefyDataProvider<ExtraData> {
	/// Return a vector of bytes, ideally should be a merkle root hash
	fn extra_data() -> ExtraData;
}

/// A default implementation for runtimes.
impl BeefyDataProvider<Vec<u8>> for () {
	fn extra_data() -> Vec<u8> {
		Vec::new()
	}
}

/// A standard leaf that gets added every block to the MMR constructed by Substrate's `pallet_mmr`.
#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
pub struct MmrLeaf<BlockNumber, Hash, MerkleRoot, ExtraData> {
	/// Version of the leaf format.
	///
	/// Can be used to enable future format migrations and compatibility.
	/// See [`MmrLeafVersion`] documentation for details.
	pub version: MmrLeafVersion,
	/// Current block parent number and hash.
	pub parent_number_and_hash: (BlockNumber, Hash),
	/// A merkle root of the next BEEFY authority set.
	pub beefy_next_authority_set: BeefyNextAuthoritySet<MerkleRoot>,
	/// Arbitrary extra leaf data to be used by downstream pallets to include custom data in the
	/// [`MmrLeaf`]
	pub leaf_extra: ExtraData,
}

/// A MMR leaf versioning scheme.
///
/// Version is a single byte that constist of two components:
/// - `major` - 3 bits
/// - `minor` - 5 bits
///
/// Any change in encoding that adds new items to the structure is considered non-breaking, hence
/// only requires an update of `minor` version. Any backward incompatible change (i.e. decoding to a
/// previous leaf format fails) should be indicated with `major` version bump.
///
/// Given that adding new struct elements in SCALE is backward compatible (i.e. old format can be
/// still decoded, the new fields will simply be ignored). We expect the major version to be bumped
/// very rarely (hopefuly never).
#[derive(Debug, Default, PartialEq, Eq, Clone, Encode, Decode)]
pub struct MmrLeafVersion(u8);
impl MmrLeafVersion {
	/// Create new version object from `major` and `minor` components.
	///
	/// Panics if any of the component occupies more than 4 bits.
	pub fn new(major: u8, minor: u8) -> Self {
		if major > 0b111 || minor > 0b11111 {
			panic!("Version components are too big.");
		}
		let version = (major << 5) + minor;
		Self(version)
	}

	/// Split the version into `major` and `minor` sub-components.
	pub fn split(&self) -> (u8, u8) {
		let major = self.0 >> 5;
		let minor = self.0 & 0b11111;
		(major, minor)
	}
}

/// Details of a BEEFY authority set.
#[derive(Debug, Default, PartialEq, Eq, Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub struct BeefyAuthoritySet<MerkleRoot> {
	/// Id of the set.
	///
	/// Id is required to correlate BEEFY signed commitments with the validator set.
	/// Light Client can easily verify that the commitment witness it is getting is
	/// produced by the latest validator set.
	pub id: crate::ValidatorSetId,
	/// Number of validators in the set.
	///
	/// Some BEEFY Light Clients may use an interactive protocol to verify only a subset
	/// of signatures. We put set length here, so that these clients can verify the minimal
	/// number of required signatures.
	pub len: u32,
	/// Merkle Root Hash built from BEEFY AuthorityIds.
	///
	/// This is used by Light Clients to confirm that the commitments are signed by the correct
	/// validator set. Light Clients using interactive protocol, might verify only subset of
	/// signatures, hence don't require the full list here (will receive inclusion proofs).
	pub root: MerkleRoot,
}

/// Details of the next BEEFY authority set.
pub type BeefyNextAuthoritySet<MerkleRoot> = BeefyAuthoritySet<MerkleRoot>;

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn should_construct_version_correctly() {
		let tests = vec![(0, 0, 0b00000000), (7, 2, 0b11100010), (7, 31, 0b11111111)];

		for (major, minor, version) in tests {
			let v = MmrLeafVersion::new(major, minor);
			assert_eq!(v.encode(), vec![version], "Encoding does not match.");
			assert_eq!(v.split(), (major, minor));
		}
	}

	#[test]
	#[should_panic]
	fn should_panic_if_major_too_large() {
		MmrLeafVersion::new(8, 0);
	}

	#[test]
	#[should_panic]
	fn should_panic_if_minor_too_large() {
		MmrLeafVersion::new(0, 32);
	}
}
