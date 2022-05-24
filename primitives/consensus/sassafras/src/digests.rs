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

//! Private implementation details of Sassafras digests.

use super::{
	AuthorityId, AuthorityIndex, AuthoritySignature, SassafrasAuthorityWeight,
	SassafrasBlockWeight, Slot, SASSAFRAS_ENGINE_ID,
};

use scale_codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

use sp_consensus_vrf::schnorrkel::{Randomness, VRFOutput, VRFProof};
use sp_runtime::{DigestItem, RuntimeDebug};
use sp_std::vec::Vec;

/// Sassafras primary slot assignment pre-digest.
#[derive(Clone, RuntimeDebug, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub struct PrimaryPreDigest {
	/// Validator index.
	pub authority_index: AuthorityIndex,
	/// Corresponding slot number.
	pub slot: Slot,
	// /// Index of ticket VRF proof that has been previously committed.
	// pub ticket_vrf_index: VRFIndex,
	// /// Attempt number of the ticket VRF proof.
	// pub ticket_vrf_attempt: u64,
	// /// Reveal of tocket VRF output.
	// pub ticket_vrf_proof: VRFProof,
	// /// Secondary "Post Block VRF" proof.
	// pub post_vrf_proof: VRFProof,
	// /// Secondary "Post Block VRF" output.
	// pub post_vrf_output: VRFOutput,
	// /// Additional commitments posted directly at pre-digest.
	// pub commitments: Vec<VRFOutput>,
}

/// Sassafras secondary slot assignment pre-digest.
#[derive(Clone, RuntimeDebug, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub struct SecondaryPreDigest {
	/// Authority index.
	pub authority_index: AuthorityIndex,
	/// Slot number.
	pub slot: Slot,
	// /// Additional commitments posted directly at pre-digest.
	// pub commitments: Vec<VRFOutput>,
}

/// A Sassafras pre-runtime digest. This contains all data required to validate a
/// block and for the Sassafras runtime module.
#[derive(Clone, RuntimeDebug, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub enum PreDigest {
	/// Primary VRF-based slot assignment.
	/// TODO-SASS: is this codec index really required here?
	#[codec(index = 1)]
	Primary(PrimaryPreDigest),
	/// Secondary deterministic slot assignment.
	#[codec(index = 2)]
	Secondary(SecondaryPreDigest),
}

impl PreDigest {
	/// Returns the slot number of the pre digest.
	pub fn authority_index(&self) -> AuthorityIndex {
		match self {
			PreDigest::Primary(primary) => primary.authority_index,
			PreDigest::Secondary(secondary) => secondary.authority_index,
		}
	}

	/// Returns the slot of the pre digest.
	pub fn slot(&self) -> Slot {
		match self {
			PreDigest::Primary(primary) => primary.slot,
			PreDigest::Secondary(secondary) => secondary.slot,
		}
	}

	/// Returns true if this pre-digest is for a primary slot assignment.
	pub fn is_primary(&self) -> bool {
		matches!(self, PreDigest::Primary(_))
	}

	/// Returns the weight _added_ by this digest, not the cumulative weight
	/// of the chain.
	pub fn added_weight(&self) -> crate::SassafrasBlockWeight {
		match self {
			PreDigest::Primary(_) => 1,
			PreDigest::Secondary(_) => 0,
		}
	}
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

/// An consensus log item for BABE.
#[derive(Decode, Encode, Clone, PartialEq, Eq)]
pub enum ConsensusLog {
	/// The epoch has changed. This provides information about the _next_
	/// epoch - information about the _current_ epoch (i.e. the one we've just
	/// entered) should already be available earlier in the chain.
	#[codec(index = 1)]
	NextEpochData(NextEpochDescriptor),
	/// Disable the authority with given index.
	#[codec(index = 2)]
	OnDisabled(AuthorityIndex),
}

/// A digest item which is usable with Sassafras consensus.
pub trait CompatibleDigestItem: Sized {
	/// Construct a digest item which contains a Sassafras pre-digest.
	fn sassafras_pre_digest(seal: PreDigest) -> Self;

	/// If this item is an Sassafras pre-digest, return it.
	fn as_sassafras_pre_digest(&self) -> Option<PreDigest>;

	/// Construct a digest item which contains a Sassafras seal.
	fn sassafras_seal(signature: AuthoritySignature) -> Self;

	/// If this item is a Sassafras signature, return the signature.
	fn as_sassafras_seal(&self) -> Option<AuthoritySignature>;

	/// If this item is a Sassafras epoch descriptor, return it.
	fn as_next_epoch_descriptor(&self) -> Option<NextEpochDescriptor>;

	// TODO-SASS
	// Add next-config-descriptor
}

impl CompatibleDigestItem for DigestItem {
	fn sassafras_pre_digest(digest: PreDigest) -> Self {
		DigestItem::PreRuntime(SASSAFRAS_ENGINE_ID, digest.encode())
	}

	fn as_sassafras_pre_digest(&self) -> Option<PreDigest> {
		self.pre_runtime_try_to(&SASSAFRAS_ENGINE_ID)
	}

	fn sassafras_seal(signature: AuthoritySignature) -> Self {
		DigestItem::Seal(SASSAFRAS_ENGINE_ID, signature.encode())
	}

	fn as_sassafras_seal(&self) -> Option<AuthoritySignature> {
		self.seal_try_to(&SASSAFRAS_ENGINE_ID)
	}

	fn as_next_epoch_descriptor(&self) -> Option<NextEpochDescriptor> {
		self.consensus_try_to(&SASSAFRAS_ENGINE_ID).and_then(|x: ConsensusLog| match x {
			ConsensusLog::NextEpochData(n) => Some(n),
			_ => None,
		})
	}
}
