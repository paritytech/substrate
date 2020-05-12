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

//! Private implementation details of BABE digests.

#[cfg(feature = "std")]
use super::{BABE_ENGINE_ID, AuthoritySignature};
use super::{AuthorityId, AuthorityIndex, SlotNumber, BabeAuthorityWeight, BabeEpochConfiguration, AllowedSlots};
#[cfg(feature = "std")]
use sp_runtime::{DigestItem, generic::OpaqueDigestItemId};
#[cfg(feature = "std")]
use std::fmt::Debug;
use codec::{Decode, Encode};
#[cfg(feature = "std")]
use codec::Codec;
use sp_std::vec::Vec;
use sp_runtime::RuntimeDebug;
use sp_consensus_vrf::schnorrkel::{Randomness, VRFOutput, VRFProof};

/// Raw BABE primary slot assignment pre-digest.
#[derive(Clone, RuntimeDebug, Encode, Decode)]
pub struct PrimaryPreDigest {
	/// Authority index
	pub authority_index: super::AuthorityIndex,
	/// Slot number
	pub slot_number: SlotNumber,
	/// VRF output
	pub vrf_output: VRFOutput,
	/// VRF proof
	pub vrf_proof: VRFProof,
}

/// BABE secondary slot assignment pre-digest.
#[derive(Clone, RuntimeDebug, Encode, Decode)]
pub struct SecondaryPlainPreDigest {
	/// Authority index
	///
	/// This is not strictly-speaking necessary, since the secondary slots
	/// are assigned based on slot number and epoch randomness. But including
	/// it makes things easier for higher-level users of the chain data to
	/// be aware of the author of a secondary-slot block.
	pub authority_index: super::AuthorityIndex,
	/// Slot number
	pub slot_number: SlotNumber,
}

/// BABE secondary deterministic slot assignment with VRF outputs.
#[derive(Clone, RuntimeDebug, Encode, Decode)]
pub struct SecondaryVRFPreDigest {
	/// Authority index
	pub authority_index: super::AuthorityIndex,
	/// Slot number
	pub slot_number: SlotNumber,
	/// VRF output
	pub vrf_output: VRFOutput,
	/// VRF proof
	pub vrf_proof: VRFProof,
}

/// A BABE pre-runtime digest. This contains all data required to validate a
/// block and for the BABE runtime module. Slots can be assigned to a primary
/// (VRF based) and to a secondary (slot number based).
#[derive(Clone, RuntimeDebug, Encode, Decode)]
pub enum PreDigest {
	/// A primary VRF-based slot assignment.
	#[codec(index = "1")]
	Primary(PrimaryPreDigest),
	/// A secondary deterministic slot assignment.
	#[codec(index = "2")]
	SecondaryPlain(SecondaryPlainPreDigest),
	/// A secondary deterministic slot assignment with VRF outputs.
	#[codec(index = "3")]
	SecondaryVRF(SecondaryVRFPreDigest),
}

impl PreDigest {
	/// Returns the slot number of the pre digest.
	pub fn authority_index(&self) -> AuthorityIndex {
		match self {
			PreDigest::Primary(primary) => primary.authority_index,
			PreDigest::SecondaryPlain(secondary) => secondary.authority_index,
			PreDigest::SecondaryVRF(secondary) => secondary.authority_index,
		}
	}

	/// Returns the slot number of the pre digest.
	pub fn slot_number(&self) -> SlotNumber {
		match self {
			PreDigest::Primary(primary) => primary.slot_number,
			PreDigest::SecondaryPlain(secondary) => secondary.slot_number,
			PreDigest::SecondaryVRF(secondary) => secondary.slot_number,
		}
	}

	/// Returns the weight _added_ by this digest, not the cumulative weight
	/// of the chain.
	pub fn added_weight(&self) -> crate::BabeBlockWeight {
		match self {
			PreDigest::Primary(_) => 1,
			PreDigest::SecondaryPlain(_) | PreDigest::SecondaryVRF(_) => 0,
		}
	}
}

/// Information about the next epoch. This is broadcast in the first block
/// of the epoch.
#[derive(Decode, Encode, PartialEq, Eq, Clone, RuntimeDebug)]
pub struct NextEpochDescriptor {
	/// The authorities.
	pub authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,

	/// The value of randomness to use for the slot-assignment.
	pub randomness: Randomness,
}

/// Information about the next epoch config, if changed. This is broadcast in the first
/// block of the epoch, and applies using the same rules as `NextEpochDescriptor`.
#[derive(Decode, Encode, PartialEq, Eq, Clone, RuntimeDebug)]
pub enum NextConfigDescriptor {
	/// Version 1.
	#[codec(index = "1")]
	V1 {
		/// Value of `c` in `BabeEpochConfiguration`.
		c: (u64, u64),
		/// Value of `allowed_slots` in `BabeEpochConfiguration`.
		allowed_slots: AllowedSlots,
	}
}

impl From<NextConfigDescriptor> for BabeEpochConfiguration {
	fn from(desc: NextConfigDescriptor) -> Self {
		match desc {
			NextConfigDescriptor::V1 { c, allowed_slots } =>
				Self { c, allowed_slots },
		}
	}
}

/// A digest item which is usable with BABE consensus.
#[cfg(feature = "std")]
pub trait CompatibleDigestItem: Sized {
	/// Construct a digest item which contains a BABE pre-digest.
	fn babe_pre_digest(seal: PreDigest) -> Self;

	/// If this item is an BABE pre-digest, return it.
	fn as_babe_pre_digest(&self) -> Option<PreDigest>;

	/// Construct a digest item which contains a BABE seal.
	fn babe_seal(signature: AuthoritySignature) -> Self;

	/// If this item is a BABE signature, return the signature.
	fn as_babe_seal(&self) -> Option<AuthoritySignature>;

	/// If this item is a BABE epoch descriptor, return it.
	fn as_next_epoch_descriptor(&self) -> Option<NextEpochDescriptor>;

	/// If this item is a BABE config descriptor, return it.
	fn as_next_config_descriptor(&self) -> Option<NextConfigDescriptor>;
}

#[cfg(feature = "std")]
impl<Hash> CompatibleDigestItem for DigestItem<Hash> where
	Hash: Debug + Send + Sync + Eq + Clone + Codec + 'static
{
	fn babe_pre_digest(digest: PreDigest) -> Self {
		DigestItem::PreRuntime(BABE_ENGINE_ID, digest.encode())
	}

	fn as_babe_pre_digest(&self) -> Option<PreDigest> {
		self.try_to(OpaqueDigestItemId::PreRuntime(&BABE_ENGINE_ID))
	}

	fn babe_seal(signature: AuthoritySignature) -> Self {
		DigestItem::Seal(BABE_ENGINE_ID, signature.encode())
	}

	fn as_babe_seal(&self) -> Option<AuthoritySignature> {
		self.try_to(OpaqueDigestItemId::Seal(&BABE_ENGINE_ID))
	}

	fn as_next_epoch_descriptor(&self) -> Option<NextEpochDescriptor> {
		self.try_to(OpaqueDigestItemId::Consensus(&BABE_ENGINE_ID))
			.and_then(|x: super::ConsensusLog| match x {
				super::ConsensusLog::NextEpochData(n) => Some(n),
				_ => None,
			})
	}

	fn as_next_config_descriptor(&self) -> Option<NextConfigDescriptor> {
		self.try_to(OpaqueDigestItemId::Consensus(&BABE_ENGINE_ID))
			.and_then(|x: super::ConsensusLog| match x {
				super::ConsensusLog::NextConfigData(n) => Some(n),
				_ => None,
			})
	}
}
