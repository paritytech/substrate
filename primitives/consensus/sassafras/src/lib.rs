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

//! Primitives for Sassafras.

// #![deny(warnings)]
// #![forbid(unsafe_code, missing_docs, unused_variables, unused_imports)]
#![cfg_attr(not(feature = "std"), no_std)]

pub mod digest;
pub mod inherents;
mod vrf;

pub use crate::vrf::{
	VRF_PROOF_LENGTH, VRF_OUTPUT_LENGTH, RawVRFOutput, VRFOutput,
	RawVRFProof, VRFProof, Randomness,
};

use sp_runtime::ConsensusEngineId;

mod app {
	use sp_application_crypto::{app_crypto, key_types::SASSAFRAS, sr25519};
	app_crypto!(sr25519, SASSAFRAS);
}

/// The prefix used by Sassafras for its ticket VRF keys.
pub const SASSAFRAS_TICKET_VRF_PREFIX: &[u8] = b"substrate-sassafras-ticket-vrf";

/// The prefix used by Sassafras for its post-block VRF keys.
pub const SASSAFRAS_POST_VRF_PREFIX: &[u8] = b"substrate-sassafras-post-vrf";

/// A slot number.
pub type SlotNumber = u64;

/// An epoch number.
pub type EpochNumber = u64;

/// A Sassafras authority keypair, used by both ticket VRF and post-block VRF.
#[cfg(feature = "std")]
pub type AuthorityPair = app::Pair;

/// A Sassafras authority signature.
pub type AuthoritySignature = app::Signature;

/// A Sassafras authority identifier.
pub type AuthorityId = app::Public;

/// The `ConsensusEngineId` of Sassafras.
pub const SASSAFRAS_ENGINE_ID: ConsensusEngineId = *b"SASS";

/// Index of ticket VRF.
pub type VRFIndex = u32;

/// The index of an authority.
pub type AuthorityIndex = u32;

/// The weight of an authority.
// NOTE: we use a unique name for the weight to avoid conflicts with other
//       `Weight` types, since the metadata isn't able to disambiguate.
pub type SassafrasAuthorityWeight = u64;

/// The weight of a Sassafras block.
pub type SassafrasBlockWeight = u32;
