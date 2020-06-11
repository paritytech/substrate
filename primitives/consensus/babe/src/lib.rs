// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

pub use merlin::Transcript;
pub use sp_consensus_vrf::schnorrkel::{
	Randomness, RANDOMNESS_LENGTH, VRF_OUTPUT_LENGTH, VRF_PROOF_LENGTH,
};

use codec::{Decode, Encode};
use sp_runtime::{traits::Header, ConsensusEngineId, RuntimeDebug};
use sp_std::vec::Vec;

use crate::digests::{NextConfigDescriptor, NextEpochDescriptor};

/// Key type for BABE module.
pub const KEY_TYPE: sp_core::crypto::KeyTypeId = sp_application_crypto::key_types::BABE;

mod app {
	use sp_application_crypto::{app_crypto, key_types::BABE, sr25519};
	app_crypto!(sr25519, BABE);
}

/// The prefix used by BABE for its VRF keys.
pub const BABE_VRF_PREFIX: &[u8] = b"substrate-babe-vrf";

/// BABE VRFInOut context.
pub static BABE_VRF_INOUT_CONTEXT: &[u8] = b"BabeVRFInOutContext";

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

/// A slot number.
pub use sp_consensus_slots::SlotNumber;

/// An equivocation proof for multiple block authorships on the same slot (i.e. double vote).
pub type EquivocationProof<H> = sp_consensus_slots::EquivocationProof<H, AuthorityId>;

/// The weight of an authority.
// NOTE: we use a unique name for the weight to avoid conflicts with other
//       `Weight` types, since the metadata isn't able to disambiguate.
pub type BabeAuthorityWeight = u64;

/// The weight of a BABE block.
pub type BabeBlockWeight = u32;

/// Make a VRF transcript from given randomness, slot number and epoch.
pub fn make_transcript(
	randomness: &Randomness,
	slot_number: u64,
	epoch: u64,
) -> Transcript {
	let mut transcript = Transcript::new(&BABE_ENGINE_ID);
	transcript.append_u64(b"slot number", slot_number);
	transcript.append_u64(b"current epoch", epoch);
	transcript.append_message(b"chain randomness", &randomness[..]);
	transcript
}

/// An consensus log item for BABE.
#[derive(Decode, Encode, Clone, PartialEq, Eq)]
pub enum ConsensusLog {
	/// The epoch has changed. This provides information about the _next_
	/// epoch - information about the _current_ epoch (i.e. the one we've just
	/// entered) should already be available earlier in the chain.
	#[codec(index = "1")]
	NextEpochData(NextEpochDescriptor),
	/// Disable the authority with given index.
	#[codec(index = "2")]
	OnDisabled(AuthorityIndex),
	/// The epoch has changed, and the epoch after the current one will
	/// enact different epoch configurations.
	#[codec(index = "3")]
	NextConfigData(NextConfigDescriptor),
}

/// Configuration data used by the BABE consensus engine.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug)]
pub struct BabeGenesisConfigurationV1 {
	/// The slot duration in milliseconds for BABE. Currently, only
	/// the value provided by this type at genesis will be used.
	///
	/// Dynamic slot duration may be supported in the future.
	pub slot_duration: u64,

	/// The duration of epochs in slots.
	pub epoch_length: SlotNumber,

	/// A constant value that is used in the threshold calculation formula.
	/// Expressed as a rational where the first member of the tuple is the
	/// numerator and the second is the denominator. The rational should
	/// represent a value between 0 and 1.
	/// In the threshold formula calculation, `1 - c` represents the probability
	/// of a slot being empty.
	pub c: (u64, u64),

	/// The authorities for the genesis epoch.
	pub genesis_authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,

	/// The randomness for the genesis epoch.
	pub randomness: Randomness,

	/// Whether this chain should run with secondary slots, which are assigned
	/// in round-robin manner.
	pub secondary_slots: bool,
}

impl From<BabeGenesisConfigurationV1> for BabeGenesisConfiguration {
	fn from(v1: BabeGenesisConfigurationV1) -> Self {
		Self {
			slot_duration: v1.slot_duration,
			epoch_length: v1.epoch_length,
			c: v1.c,
			genesis_authorities: v1.genesis_authorities,
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
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug)]
pub struct BabeGenesisConfiguration {
	/// The slot duration in milliseconds for BABE. Currently, only
	/// the value provided by this type at genesis will be used.
	///
	/// Dynamic slot duration may be supported in the future.
	pub slot_duration: u64,

	/// The duration of epochs in slots.
	pub epoch_length: SlotNumber,

	/// A constant value that is used in the threshold calculation formula.
	/// Expressed as a rational where the first member of the tuple is the
	/// numerator and the second is the denominator. The rational should
	/// represent a value between 0 and 1.
	/// In the threshold formula calculation, `1 - c` represents the probability
	/// of a slot being empty.
	pub c: (u64, u64),

	/// The authorities for the genesis epoch.
	pub genesis_authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,

	/// The randomness for the genesis epoch.
	pub randomness: Randomness,

	/// Type of allowed slots.
	pub allowed_slots: AllowedSlots,
}

/// Types of allowed slots.
#[derive(Clone, Copy, PartialEq, Eq, Encode, Decode, RuntimeDebug)]
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

#[cfg(feature = "std")]
impl sp_consensus::SlotData for BabeGenesisConfiguration {
	fn slot_duration(&self) -> u64 {
		self.slot_duration
	}

	const SLOT_KEY: &'static [u8] = b"babe_configuration";
}

/// Configuration data used by the BABE consensus engine.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug)]
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

/// TODO
pub fn check_equivocation_proof<H>(proof: EquivocationProof<H>) -> Option<SlotNumber>
where
	H: Header,
{
	use digests::*;
	use sp_application_crypto::RuntimeAppPublic;

	// we must have different headers for the equivocation to be valid
	if proof.first_header.hash() == proof.second_header.hash() {
		return None;
	}

	let find_pre_digest = |header: &H| {
		header
			.digest()
			.logs()
			.iter()
			.find_map(|log| log.as_babe_pre_digest())
	};

	let first_pre_digest = find_pre_digest(&proof.first_header)?;
	let second_pre_digest = find_pre_digest(&proof.second_header)?;

	// and both headers must be targetting the same slot
	if first_pre_digest.slot_number() != second_pre_digest.slot_number() {
		return None;
	}

	// and must be authored by the same authority
	if first_pre_digest.authority_index() != second_pre_digest.authority_index() {
		return None;
	}

	let offender = proof.offender;
	let verify_seal_signature = |mut header: H| {
		let seal = header.digest_mut().pop()?.as_babe_seal()?;
		let pre_hash = header.hash();

		if !offender.verify(&pre_hash.as_ref(), &seal) {
			return None;
		}

		Some(())
	};

	// we finally verify that the expected authority has signed both headers and
	// that the signature is valid.
	verify_seal_signature(proof.first_header)?;
	verify_seal_signature(proof.second_header)?;

	Some(first_pre_digest.slot_number())
}

sp_api::decl_runtime_apis! {
	/// API necessary for block authorship with BABE.
	#[api_version(2)]
	pub trait BabeApi {
		/// Return the genesis configuration for BABE. The configuration is only read on genesis.
		fn configuration() -> BabeGenesisConfiguration;

		/// Return the configuration for BABE. Version 1.
		#[changed_in(2)]
		fn configuration() -> BabeGenesisConfigurationV1;

		/// Returns the slot number that started the current epoch.
		fn current_epoch_start() -> SlotNumber;

		/// FIXME
		fn generate_key_ownership_proof(
			authority_id: AuthorityId,
		) -> Option<Vec<u8>>;

		/// FIXME
		fn submit_report_equivocation_unsigned_extrinsic(
			equivocation_proof: EquivocationProof<Block::Header>,
			key_owner_proof: Vec<u8>,
		) -> Option<()>;
	}
}
