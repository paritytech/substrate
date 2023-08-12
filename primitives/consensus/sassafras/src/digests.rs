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
	ticket::TicketClaim, AuthorityId, AuthorityIndex, AuthoritySignature, Randomness,
	SassafrasEpochConfiguration, Slot, VrfSignature, SASSAFRAS_ENGINE_ID,
};

use scale_codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

use sp_runtime::{DigestItem, RuntimeDebug};
use sp_std::vec::Vec;

/// Sassafras slot assignment pre-digest.
#[derive(Clone, RuntimeDebug, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub struct PreDigest {
	/// Authority index that claimed the slot.
	pub authority_idx: AuthorityIndex,
	/// Corresponding slot number.
	pub slot: Slot,
	/// Slot claim VRF signature.
	pub vrf_signature: VrfSignature,
	/// Ticket auxiliary information for claim check.
	pub ticket_claim: Option<TicketClaim>,
}

/// Information about the next epoch. This is broadcast in the first block
/// of the epoch.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug)]
pub struct NextEpochDescriptor {
	/// The authorities.
	pub authorities: Vec<AuthorityId>,
	/// The value of randomness to use for the slot-assignment.
	pub randomness: Randomness,
	/// Algorithm parameters. If not present, previous epoch parameters are used.
	pub config: Option<SassafrasEpochConfiguration>,
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
}
