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

//! Primitives for BABE.
#![deny(warnings)]
#![forbid(unsafe_code, missing_docs, unused_variables, unused_imports)]
#![cfg_attr(not(feature = "std"), no_std)]

pub mod digests;
pub mod inherents;

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use sp_runtime::{traits::Header, ConsensusEngineId, RuntimeDebug};
use sp_std::vec::Vec;

use crate::digests::{NextConfigDescriptor, NextEpochDescriptor};

pub use sp_core::sr25519::vrf::{
	VrfInput, VrfOutput, VrfProof, VrfSignData, VrfSignature, VrfTranscript,
};

/// Key type for BABE module.
pub const KEY_TYPE: sp_core::crypto::KeyTypeId = sp_application_crypto::key_types::BABE;

mod app {
	use sp_application_crypto::{app_crypto, key_types::BABE, sr25519};
	app_crypto!(sr25519, BABE);
}

/// VRF context used for per-slot randomness generation.
pub const RANDOMNESS_VRF_CONTEXT: &[u8] = b"BabeVRFInOutContext";

/// VRF output length for per-slot randomness.
pub const RANDOMNESS_LENGTH: usize = 32;

/// Randomness type required by BABE operations.
pub type Randomness = [u8; RANDOMNESS_LENGTH];

/// A Babe authority keypair. Necessarily equivalent to the schnorrkel public key used in
/// the main Babe module. If that ever changes, then this must, too.
#[cfg(feature = "std")]
pub type AuthorityPair = app::Pair;

/// A Babe authority signature.
pub type AuthoritySignature = app::Signature;

/// A Babe authority identifier. Necessarily equivalent to the schnorrkel public key used in
/// the main Babe module. If that ever changes, then this must, too.
pub type AuthorityId = app::Public;

/// The `ConsensusEngineId` of BABE.
pub const BABE_ENGINE_ID: ConsensusEngineId = *b"BABE";

/// The length of the public key
pub const PUBLIC_KEY_LENGTH: usize = 32;

/// How many blocks to wait before running the median algorithm for relative time
/// This will not vary from chain to chain as it is not dependent on slot duration
/// or epoch length.
pub const MEDIAN_ALGORITHM_CARDINALITY: usize = 1200; // arbitrary suggestion by w3f-research.

/// The index of an authority.
pub type AuthorityIndex = u32;

pub use sp_consensus_slots::{Slot, SlotDuration};

/// An equivocation proof for multiple block authorships on the same slot (i.e. double vote).
pub type EquivocationProof<H> = sp_consensus_slots::EquivocationProof<H, AuthorityId>;

/// The weight of an authority.
// NOTE: we use a unique name for the weight to avoid conflicts with other
//       `Weight` types, since the metadata isn't able to disambiguate.
pub type BabeAuthorityWeight = u64;

/// The cumulative weight of a BABE block, i.e. sum of block weights starting
/// at this block until the genesis block.
///
/// Primary blocks have a weight of 1 whereas secondary blocks have a weight
/// of 0 (regardless of whether they are plain or vrf secondary blocks).
pub type BabeBlockWeight = u32;

/// Make VRF input suitable for BABE's randomness generation.
pub fn make_vrf_transcript(randomness: &Randomness, slot: Slot, epoch: u64) -> VrfInput {
	VrfInput::new(
		&BABE_ENGINE_ID,
		&[
			(b"slot number", &slot.to_le_bytes()),
			(b"current epoch", &epoch.to_le_bytes()),
			(b"chain randomness", randomness),
		],
	)
}

/// Make VRF signing data suitable for BABE's protocol.
pub fn make_vrf_sign_data(randomness: &Randomness, slot: Slot, epoch: u64) -> VrfSignData {
	make_vrf_transcript(randomness, slot, epoch).into()
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
	/// The epoch has changed, and the epoch after the current one will
	/// enact different epoch configurations.
	#[codec(index = 3)]
	NextConfigData(NextConfigDescriptor),
}

/// Configuration data used by the BABE consensus engine.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug)]
pub struct BabeConfigurationV1 {
	/// The slot duration in milliseconds for BABE. Currently, only
	/// the value provided by this type at genesis will be used.
	///
	/// Dynamic slot duration may be supported in the future.
	pub slot_duration: u64,

	/// The duration of epochs in slots.
	pub epoch_length: u64,

	/// A constant value that is used in the threshold calculation formula.
	/// Expressed as a rational where the first member of the tuple is the
	/// numerator and the second is the denominator. The rational should
	/// represent a value between 0 and 1.
	/// In the threshold formula calculation, `1 - c` represents the probability
	/// of a slot being empty.
	pub c: (u64, u64),

	/// The authorities for the genesis epoch.
	pub authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,

	/// The randomness for the genesis epoch.
	pub randomness: Randomness,

	/// Whether this chain should run with secondary slots, which are assigned
	/// in round-robin manner.
	pub secondary_slots: bool,
}

impl From<BabeConfigurationV1> for BabeConfiguration {
	fn from(v1: BabeConfigurationV1) -> Self {
		Self {
			slot_duration: v1.slot_duration,
			epoch_length: v1.epoch_length,
			c: v1.c,
			authorities: v1.authorities,
			randomness: v1.randomness,
			allowed_slots: if v1.secondary_slots {
				AllowedSlots::PrimaryAndSecondaryPlainSlots
			} else {
				AllowedSlots::PrimarySlots
			},
		}
	}
}

/// Configuration data used by the BABE consensus engine.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct BabeConfiguration {
	/// The slot duration in milliseconds for BABE. Currently, only
	/// the value provided by this type at genesis will be used.
	///
	/// Dynamic slot duration may be supported in the future.
	pub slot_duration: u64,

	/// The duration of epochs in slots.
	pub epoch_length: u64,

	/// A constant value that is used in the threshold calculation formula.
	/// Expressed as a rational where the first member of the tuple is the
	/// numerator and the second is the denominator. The rational should
	/// represent a value between 0 and 1.
	/// In the threshold formula calculation, `1 - c` represents the probability
	/// of a slot being empty.
	pub c: (u64, u64),

	/// The authorities
	pub authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,

	/// The randomness
	pub randomness: Randomness,

	/// Type of allowed slots.
	pub allowed_slots: AllowedSlots,
}

impl BabeConfiguration {
	/// Convenience method to get the slot duration as a `SlotDuration` value.
	pub fn slot_duration(&self) -> SlotDuration {
		SlotDuration::from_millis(self.slot_duration)
	}
}

/// Types of allowed slots.
#[derive(Clone, Copy, PartialEq, Eq, Encode, Decode, RuntimeDebug, MaxEncodedLen, TypeInfo)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum AllowedSlots {
	/// Only allow primary slots.
	PrimarySlots,
	/// Allow primary and secondary plain slots.
	PrimaryAndSecondaryPlainSlots,
	/// Allow primary and secondary VRF slots.
	PrimaryAndSecondaryVRFSlots,
}

impl AllowedSlots {
	/// Whether plain secondary slots are allowed.
	pub fn is_secondary_plain_slots_allowed(&self) -> bool {
		*self == Self::PrimaryAndSecondaryPlainSlots
	}

	/// Whether VRF secondary slots are allowed.
	pub fn is_secondary_vrf_slots_allowed(&self) -> bool {
		*self == Self::PrimaryAndSecondaryVRFSlots
	}
}

/// Configuration data used by the BABE consensus engine that may change with epochs.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, MaxEncodedLen, TypeInfo)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct BabeEpochConfiguration {
	/// A constant value that is used in the threshold calculation formula.
	/// Expressed as a rational where the first member of the tuple is the
	/// numerator and the second is the denominator. The rational should
	/// represent a value between 0 and 1.
	/// In the threshold formula calculation, `1 - c` represents the probability
	/// of a slot being empty.
	pub c: (u64, u64),

	/// Whether this chain should run with secondary slots, which are assigned
	/// in round-robin manner.
	pub allowed_slots: AllowedSlots,
}

/// Verifies the equivocation proof by making sure that: both headers have
/// different hashes, are targetting the same slot, and have valid signatures by
/// the same authority.
pub fn check_equivocation_proof<H>(proof: EquivocationProof<H>) -> bool
where
	H: Header,
{
	use digests::*;
	use sp_application_crypto::RuntimeAppPublic;

	let find_pre_digest =
		|header: &H| header.digest().logs().iter().find_map(|log| log.as_babe_pre_digest());

	let verify_seal_signature = |mut header: H, offender: &AuthorityId| {
		let seal = header.digest_mut().pop()?.as_babe_seal()?;
		let pre_hash = header.hash();

		if !offender.verify(&pre_hash.as_ref(), &seal) {
			return None
		}

		Some(())
	};

	let verify_proof = || {
		// we must have different headers for the equivocation to be valid
		if proof.first_header.hash() == proof.second_header.hash() {
			return None
		}

		let first_pre_digest = find_pre_digest(&proof.first_header)?;
		let second_pre_digest = find_pre_digest(&proof.second_header)?;

		// both headers must be targetting the same slot and it must
		// be the same as the one in the proof.
		if proof.slot != first_pre_digest.slot() ||
			first_pre_digest.slot() != second_pre_digest.slot()
		{
			return None
		}

		// both headers must have been authored by the same authority
		if first_pre_digest.authority_index() != second_pre_digest.authority_index() {
			return None
		}

		// we finally verify that the expected authority has signed both headers and
		// that the signature is valid.
		verify_seal_signature(proof.first_header, &proof.offender)?;
		verify_seal_signature(proof.second_header, &proof.offender)?;

		Some(())
	};

	// NOTE: we isolate the verification code into an helper function that
	// returns `Option<()>` so that we can use `?` to deal with any intermediate
	// errors and discard the proof as invalid.
	verify_proof().is_some()
}

/// An opaque type used to represent the key ownership proof at the runtime API
/// boundary. The inner value is an encoded representation of the actual key
/// ownership proof which will be parameterized when defining the runtime. At
/// the runtime API boundary this type is unknown and as such we keep this
/// opaque representation, implementors of the runtime API will have to make
/// sure that all usages of `OpaqueKeyOwnershipProof` refer to the same type.
#[derive(Decode, Encode, PartialEq, TypeInfo)]
pub struct OpaqueKeyOwnershipProof(Vec<u8>);
impl OpaqueKeyOwnershipProof {
	/// Create a new `OpaqueKeyOwnershipProof` using the given encoded
	/// representation.
	pub fn new(inner: Vec<u8>) -> OpaqueKeyOwnershipProof {
		OpaqueKeyOwnershipProof(inner)
	}

	/// Try to decode this `OpaqueKeyOwnershipProof` into the given concrete key
	/// ownership proof type.
	pub fn decode<T: Decode>(self) -> Option<T> {
		Decode::decode(&mut &self.0[..]).ok()
	}
}

/// BABE epoch information
#[derive(Decode, Encode, PartialEq, Eq, Clone, Debug, TypeInfo)]
pub struct Epoch {
	/// The epoch index.
	pub epoch_index: u64,
	/// The starting slot of the epoch.
	pub start_slot: Slot,
	/// The duration of this epoch.
	pub duration: u64,
	/// The authorities and their weights.
	pub authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,
	/// Randomness for this epoch.
	pub randomness: Randomness,
	/// Configuration of the epoch.
	pub config: BabeEpochConfiguration,
}

/// Returns the epoch index the given slot belongs to.
pub fn epoch_index(slot: Slot, genesis_slot: Slot, epoch_duration: u64) -> u64 {
	*slot.saturating_sub(genesis_slot) / epoch_duration
}

/// Returns the first slot at the given epoch index.
pub fn epoch_start_slot(epoch_index: u64, genesis_slot: Slot, epoch_duration: u64) -> Slot {
	// (epoch_index * epoch_duration) + genesis_slot

	const PROOF: &str = "slot number is u64; it should relate in some way to wall clock time; \
						 if u64 is not enough we should crash for safety; qed.";

	epoch_index
		.checked_mul(epoch_duration)
		.and_then(|slot| slot.checked_add(*genesis_slot))
		.expect(PROOF)
		.into()
}

sp_api::decl_runtime_apis! {
	/// API necessary for block authorship with BABE.
	#[api_version(2)]
	pub trait BabeApi {
		/// Return the configuration for BABE.
		fn configuration() -> BabeConfiguration;

		/// Return the configuration for BABE. Version 1.
		#[changed_in(2)]
		fn configuration() -> BabeConfigurationV1;

		/// Returns the slot that started the current epoch.
		fn current_epoch_start() -> Slot;

		/// Returns information regarding the current epoch.
		fn current_epoch() -> Epoch;

		/// Returns information regarding the next epoch (which was already
		/// previously announced).
		fn next_epoch() -> Epoch;

		/// Generates a proof of key ownership for the given authority in the
		/// current epoch. An example usage of this module is coupled with the
		/// session historical module to prove that a given authority key is
		/// tied to a given staking identity during a specific session. Proofs
		/// of key ownership are necessary for submitting equivocation reports.
		/// NOTE: even though the API takes a `slot` as parameter the current
		/// implementations ignores this parameter and instead relies on this
		/// method being called at the correct block height, i.e. any point at
		/// which the epoch for the given slot is live on-chain. Future
		/// implementations will instead use indexed data through an offchain
		/// worker, not requiring older states to be available.
		fn generate_key_ownership_proof(
			slot: Slot,
			authority_id: AuthorityId,
		) -> Option<OpaqueKeyOwnershipProof>;

		/// Submits an unsigned extrinsic to report an equivocation. The caller
		/// must provide the equivocation proof and a key ownership proof
		/// (should be obtained using `generate_key_ownership_proof`). The
		/// extrinsic will be unsigned and should only be accepted for local
		/// authorship (not to be broadcast to the network). This method returns
		/// `None` when creation of the extrinsic fails, e.g. if equivocation
		/// reporting is disabled for the given runtime (i.e. this method is
		/// hardcoded to return `None`). Only useful in an offchain context.
		fn submit_report_equivocation_unsigned_extrinsic(
			equivocation_proof: EquivocationProof<Block::Header>,
			key_owner_proof: OpaqueKeyOwnershipProof,
		) -> Option<()>;
	}
}
