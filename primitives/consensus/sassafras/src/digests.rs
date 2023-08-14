// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Sassafras digests structures and helpers.

use crate::{
	ticket::TicketClaim, AuthorityId, AuthorityIndex, AuthoritySignature, EpochConfiguration,
	Randomness, Slot, VrfSignature, SASSAFRAS_ENGINE_ID,
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

/// Information about the next epoch.
///
/// This is broadcast in the first block of each epoch.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug)]
pub struct NextEpochDescriptor {
	/// Authorities list.
	pub authorities: Vec<AuthorityId>,
	/// Epoch randomness.
	pub randomness: Randomness,
	/// Mutable epoch parameters. If not present previous epoch parameters are used.
	pub config: Option<EpochConfiguration>,
}

/// Consensus log item.
#[derive(Decode, Encode, Clone, PartialEq, Eq)]
pub enum ConsensusLog {
	/// Provides information about the next epoch parameters.
	#[codec(index = 1)]
	NextEpochData(NextEpochDescriptor),
	/// Disable the authority with given index.
	#[codec(index = 2)]
	OnDisabled(AuthorityIndex),
}

/// A digest item which is usable by Sassafras.
pub trait CompatibleDigestItem {
	/// Construct a digest item which contains a `PreDigest`.
	fn sassafras_pre_digest(seal: PreDigest) -> Self;

	/// If this item is a `PreDigest`, return it.
	fn as_sassafras_pre_digest(&self) -> Option<PreDigest>;

	/// Construct a digest item which contains an `AuthoritySignature`.
	fn sassafras_seal(signature: AuthoritySignature) -> Self;

	/// If this item is an `AuthoritySignature`, return it.
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
