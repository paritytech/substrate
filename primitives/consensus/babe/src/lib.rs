// Copyright 2019 Parity Technologies (UK) Ltd.
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

mod digest;
pub mod inherents;

use codec::{Encode, Decode};
use rstd::vec::Vec;
use sr_primitives::{ConsensusEngineId, RuntimeDebug};

#[cfg(feature = "std")]
pub use digest::{BabePreDigest, CompatibleDigestItem};
pub use digest::{BABE_VRF_PREFIX, RawBabePreDigest, NextEpochDescriptor};

mod app {
	use app_crypto::{app_crypto, key_types::BABE, sr25519};
	app_crypto!(sr25519, BABE);
}

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

/// The length of the VRF output
pub const VRF_OUTPUT_LENGTH: usize = 32;

/// The length of the VRF proof
pub const VRF_PROOF_LENGTH: usize = 64;

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

/// BABE epoch information
#[derive(Decode, Encode, Default, PartialEq, Eq, Clone, RuntimeDebug)]
pub struct Epoch {
	/// The epoch index
	pub epoch_index: u64,
	/// The starting slot of the epoch,
	pub start_slot: SlotNumber,
	/// The duration of this epoch
	pub duration: SlotNumber,
	/// The authorities and their weights
	pub authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,
	/// Randomness for this epoch
	pub randomness: [u8; VRF_OUTPUT_LENGTH],
}

impl Epoch {
	/// "increment" the epoch, with given descriptor for the next.
	pub fn increment(&self, descriptor: NextEpochDescriptor) -> Epoch {
		Epoch {
			epoch_index: self.epoch_index + 1,
			start_slot: self.start_slot + self.duration,
			duration: self.duration,
			authorities: descriptor.authorities,
			randomness: descriptor.randomness,
		}
	}

	/// Produce the "end slot" of the epoch. This is NOT inclusive to the epoch,
	// i.e. the slots covered by the epoch are `self.start_slot .. self.end_slot()`.
	pub fn end_slot(&self) -> SlotNumber {
		self.start_slot + self.duration
	}
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
}

/// Configuration data used by the BABE consensus engine.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug)]
pub struct BabeConfiguration {
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
	pub randomness: [u8; VRF_OUTPUT_LENGTH],

	/// Whether this chain should run with secondary slots, which are assigned
	/// in round-robin manner.
	pub secondary_slots: bool,
}

#[cfg(feature = "std")]
impl slots::SlotData for BabeConfiguration {
	fn slot_duration(&self) -> u64 {
		self.slot_duration
	}

	const SLOT_KEY: &'static [u8] = b"babe_configuration";
}

sr_api::decl_runtime_apis! {
	/// API necessary for block authorship with BABE.
	pub trait BabeApi {
		/// Return the configuration for BABE. Currently,
		/// only the value provided by this type at genesis will be used.
		///
		/// Dynamic configuration may be supported in the future.
		fn configuration() -> BabeConfiguration;
	}
}
