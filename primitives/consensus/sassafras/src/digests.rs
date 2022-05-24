// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Private implementation details of Sassafras digests.

use super::{AuthorityId, SassafrasAuthorityWeight};

use scale_codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

use sp_consensus_vrf::schnorrkel::{Randomness, VRFOutput, VRFProof};
use sp_runtime::{DigestItem, RuntimeDebug};
use sp_std::vec::Vec;

/// A Sassafras pre-runtime digest. This contains all data required to validate a
/// block and for the Sassafras runtime module.
#[derive(Clone, RuntimeDebug, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub struct PreDigest {
	// TODO
}

/// Information about the next epoch. This is broadcast in the first block
/// of the epoch.
#[derive(Decode, Encode, PartialEq, Eq, Clone, RuntimeDebug)]
pub struct NextEpochDescriptor {
	/// The authorities.
	pub authorities: Vec<(AuthorityId, SassafrasAuthorityWeight)>,
	/// The value of randomness to use for the slot-assignment.
	pub randomness: Randomness,
}
