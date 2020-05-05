// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Primitives for BABE.
#![deny(warnings)]
#![forbid(unsafe_code, missing_docs, unused_variables, unused_imports)]
#![cfg_attr(not(feature = "std"), no_std)]

pub mod digests;
pub mod inherents;

pub use sp_consensus_vrf::schnorrkel::{
	Randomness, VRF_PROOF_LENGTH, VRF_OUTPUT_LENGTH, RANDOMNESS_LENGTH
};
pub use merlin::Transcript;

use codec::{Encode, Decode};
use sp_std::vec::Vec;
use sp_runtime::{ConsensusEngineId, RuntimeDebug};
use crate::digests::{NextEpochDescriptor, NextConfigDescriptor};

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
pub type SlotNumber = u64;

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
	}
}
