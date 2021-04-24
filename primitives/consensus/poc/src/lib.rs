// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// Copyright (C) 2021 Subpace Labs, Inc.
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

//! Primitives for PoC.
#![deny(warnings)]
#![forbid(unsafe_code, missing_docs, unused_variables, unused_imports)]
#![cfg_attr(not(feature = "std"), no_std)]

pub mod digests;
pub mod inherents;

// TODO: these should change with PoR
pub use merlin::Transcript;
pub use sp_consensus_vrf::schnorrkel::{
	Randomness, RANDOMNESS_LENGTH, VRF_OUTPUT_LENGTH, VRF_PROOF_LENGTH,
};

use codec::{Decode, Encode};
#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
#[cfg(feature = "std")]
use sp_keystore::vrf::{VRFTranscriptData, VRFTranscriptValue};
use sp_runtime::{/*traits::Header, */ConsensusEngineId, RuntimeDebug};

use crate::digests::{NextConfigDescriptor, NextEpochDescriptor};

/// Key type for PoC module.
pub const KEY_TYPE: sp_core::crypto::KeyTypeId = sp_application_crypto::key_types::POC;

mod app {
	use sp_application_crypto::{app_crypto, key_types::POC, sr25519};
	app_crypto!(sr25519, POC);
}

// TODO: may be able to remove both of these

/// The prefix used by PoC for its VRF keys.
pub const POC_VRF_PREFIX: &[u8] = b"substrate-poc-vrf";

/// PoC VRFInOut context.
pub static POC_VRF_INOUT_CONTEXT: &[u8] = b"PoCVRFInOutContext";

/// A PoC farmer signature.
pub type FarmerSignature = app::Signature;

/// A PoC farmer identifier. Necessarily equivalent to the schnorrkel public key used in
/// the main PoC module. If that ever changes, then this must, too.
pub type FarmerId = app::Public;

/// The `ConsensusEngineId` of PoC.
pub const POC_ENGINE_ID: ConsensusEngineId = *b"POC0";

/// The length of the public key
pub const PUBLIC_KEY_LENGTH: usize = 32;

/// How many blocks to wait before running the median algorithm for relative time
/// This will not vary from chain to chain as it is not dependent on slot duration
/// or epoch length.
pub const MEDIAN_ALGORITHM_CARDINALITY: usize = 1200; // arbitrary suggestion by w3f-research.

pub use sp_consensus_slots::Slot;

// /// An equivocation proof for multiple block authorships on the same slot (i.e. double vote).
// pub type EquivocationProof<H> = sp_consensus_slots::EquivocationProof<H, FarmerId>;

/// The weight of a PoC block.
pub type PoCBlockWeight = u32;

// TODO: can this be removed?

/// Make a VRF transcript from given randomness, slot number and epoch.
pub fn make_transcript(
	randomness: &Randomness,
	slot: Slot,
	epoch: u64,
) -> Transcript {
	let mut transcript = Transcript::new(&POC_ENGINE_ID);
	transcript.append_u64(b"slot number", *slot);
	transcript.append_u64(b"current epoch", epoch);
	transcript.append_message(b"chain randomness", &randomness[..]);
	transcript
}

/// Make a VRF transcript data container
#[cfg(feature = "std")]
pub fn make_transcript_data(
	randomness: &Randomness,
	slot: Slot,
	epoch: u64,
) -> VRFTranscriptData {
	VRFTranscriptData {
		label: &POC_ENGINE_ID,
		items: vec![
			("slot number", VRFTranscriptValue::U64(*slot)),
			("current epoch", VRFTranscriptValue::U64(epoch)),
			("chain randomness", VRFTranscriptValue::Bytes(randomness.to_vec())),
		]
	}
}

/// An consensus log item for BABE.
#[derive(Decode, Encode, Clone, PartialEq, Eq)]
pub enum ConsensusLog {
	/// The epoch has changed. This provides information about the _next_
	/// epoch - information about the _current_ epoch (i.e. the one we've just
	/// entered) should already be available earlier in the chain.
	#[codec(index = 1)]
	NextEpochData(NextEpochDescriptor),
	/// The epoch has changed, and the epoch after the current one will
	/// enact different epoch configurations.
	#[codec(index = 2)]
	NextConfigData(NextConfigDescriptor),
}

/// Configuration data used by the PoC consensus engine.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug)]
pub struct PoCGenesisConfiguration {
	/// The slot duration in milliseconds for PoC. Currently, only
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

	/// The randomness for the genesis epoch.
	pub randomness: Randomness,
}

#[cfg(feature = "std")]
impl sp_consensus::SlotData for PoCGenesisConfiguration {
	fn slot_duration(&self) -> std::time::Duration {
		std::time::Duration::from_millis(self.slot_duration)
	}

	const SLOT_KEY: &'static [u8] = b"poc_configuration";
}

/// Configuration data used by the PoC consensus engine.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct PoCEpochConfiguration {
	/// A constant value that is used in the threshold calculation formula.
	/// Expressed as a rational where the first member of the tuple is the
	/// numerator and the second is the denominator. The rational should
	/// represent a value between 0 and 1.
	/// In the threshold formula calculation, `1 - c` represents the probability
	/// of a slot being empty.
	pub c: (u64, u64),
}

// TODO: bring this back in for Milestone 3

// /// Verifies the equivocation proof by making sure that: both headers have
// /// different hashes, are targeting the same slot, and have valid signatures by
// /// the same authority.
// pub fn check_equivocation_proof<H>(proof: EquivocationProof<H>) -> bool
// where
// 	H: Header,
// {
// 	use digests::*;
// 	use sp_application_crypto::RuntimeAppPublic;
//
// 	let find_pre_digest = |header: &H| {
// 		header
// 			.digest()
// 			.logs()
// 			.iter()
// 			.find_map(|log| log.as_poc_pre_digest())
// 	};
//
// 	let verify_seal_signature = |mut header: H, offender: &FarmerId| {
// 		let seal = header.digest_mut().pop()?.as_poc_seal()?;
// 		let pre_hash = header.hash();
//
// 		if !offender.verify(&pre_hash.as_ref(), &seal) {
// 			return None;
// 		}
//
// 		Some(())
// 	};
//
// 	let verify_proof = || {
// 		// we must have different headers for the equivocation to be valid
// 		if proof.first_header.hash() == proof.second_header.hash() {
// 			return None;
// 		}
//
// 		let first_pre_digest = find_pre_digest(&proof.first_header)?;
// 		let second_pre_digest = find_pre_digest(&proof.second_header)?;
//
// 		// both headers must be targeting the same slot and it must
// 		// be the same as the one in the proof.
// 		if proof.slot != first_pre_digest.slot ||
// 			first_pre_digest.slot != second_pre_digest.slot
// 		{
// 			return None;
// 		}
//
// 		// TODO: Replace with FarmerId
// 		// // both headers must have been authored by the same authority
// 		// if first_pre_digest.authority_index() != second_pre_digest.authority_index() {
// 		// 	return None;
// 		// }
//
// 		// we finally verify that the expected farmer has signed both headers and
// 		// that the signature is valid.
// 		verify_seal_signature(proof.first_header, &proof.offender)?;
// 		verify_seal_signature(proof.second_header, &proof.offender)?;
//
// 		Some(())
// 	};
//
// 	// NOTE: we isolate the verification code into an helper function that
// 	// returns `Option<()>` so that we can use `?` to deal with any intermediate
// 	// errors and discard the proof as invalid.
// 	verify_proof().is_some()
// }
//
// /// An opaque type used to represent the key ownership proof at the runtime API
// /// boundary. The inner value is an encoded representation of the actual key
// /// ownership proof which will be parameterized when defining the runtime. At
// /// the runtime API boundary this type is unknown and as such we keep this
// /// opaque representation, implementors of the runtime API will have to make
// /// sure that all usages of `OpaqueKeyOwnershipProof` refer to the same type.
// #[derive(Decode, Encode, PartialEq)]
// pub struct OpaqueKeyOwnershipProof(Vec<u8>);
// impl OpaqueKeyOwnershipProof {
// 	/// Create a new `OpaqueKeyOwnershipProof` using the given encoded
// 	/// representation.
// 	pub fn new(inner: Vec<u8>) -> OpaqueKeyOwnershipProof {
// 		OpaqueKeyOwnershipProof(inner)
// 	}
//
// 	/// Try to decode this `OpaqueKeyOwnershipProof` into the given concrete key
// 	/// ownership proof type.
// 	pub fn decode<T: Decode>(self) -> Option<T> {
// 		Decode::decode(&mut &self.0[..]).ok()
// 	}
// }

/// PoC epoch information
#[derive(Decode, Encode, PartialEq, Eq, Clone, Debug)]
pub struct Epoch {
	/// The epoch index.
	pub epoch_index: u64,
	/// The starting slot of the epoch.
	pub start_slot: Slot,
	/// The duration of this epoch.
	pub duration: u64,
	/// Randomness for this epoch.
	pub randomness: [u8; VRF_OUTPUT_LENGTH],
	/// Configuration of the epoch.
	pub config: PoCEpochConfiguration,
}

sp_api::decl_runtime_apis! {
	/// API necessary for block authorship with PoC.
	pub trait PoCApi {
		/// Return the genesis configuration for PoC. The configuration is only read on genesis.
		fn configuration() -> PoCGenesisConfiguration;

		/// Returns the slot that started the current epoch.
		fn current_epoch_start() -> Slot;

		/// Returns information regarding the current epoch.
		fn current_epoch() -> Epoch;

		/// Returns information regarding the next epoch (which was already
		/// previously announced).
		fn next_epoch() -> Epoch;

		// TODO: fix this in milestone 3

		// /// Submits an unsigned extrinsic to report an equivocation. The caller
		// /// must provide the equivocation proof and a key ownership proof
		// /// (should be obtained using `generate_key_ownership_proof`). The
		// /// extrinsic will be unsigned and should only be accepted for local
		// /// authorship (not to be broadcast to the network). This method returns
		// /// `None` when creation of the extrinsic fails, e.g. if equivocation
		// /// reporting is disabled for the given runtime (i.e. this method is
		// /// hardcoded to return `None`). Only useful in an offchain context.
		// fn submit_report_equivocation_unsigned_extrinsic(
		// 	equivocation_proof: EquivocationProof<Block::Header>,
		// 	key_owner_proof: OpaqueKeyOwnershipProof,
		// ) -> Option<()>;
	}
}
