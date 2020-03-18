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
use super::{AuthorityId, AuthorityIndex, SlotNumber, BabeAuthorityWeight};
#[cfg(feature = "std")]
use sp_runtime::{DigestItem, generic::OpaqueDigestItemId};
#[cfg(feature = "std")]
use std::{fmt::Debug, convert::{TryFrom, TryInto}};
use codec::{Decode, Encode};
#[cfg(feature = "std")]
use codec::Codec;
use sp_std::vec::Vec;
use sp_consensus_vrf::schnorrkel::{self, Randomness};
#[cfg(feature = "std")]
use sp_consensus_vrf::schnorrkel::SignatureError;

/// A BABE pre-runtime digest. This contains all data required to validate a
/// block and for the BABE runtime module. Slots can be assigned to a primary
/// (VRF based) and to a secondary (slot number based).
#[derive(Clone, Debug, Encode, Decode)]
pub enum RawPreDigest<VRFOutput=schnorrkel::RawVRFOutput, VRFProof=schnorrkel::RawVRFProof> {
	/// A primary VRF-based slot assignment.
	#[codec(index = "1")]
	Primary {
		/// Authority index
		authority_index: super::AuthorityIndex,
		/// Slot number
		slot_number: SlotNumber,
		/// VRF output
		vrf_output: VRFOutput,
		/// VRF proof
		vrf_proof: VRFProof,
	},
	/// A secondary deterministic slot assignment.
	#[codec(index = "2")]
	Secondary {
		/// Authority index
		///
		/// This is not strictly-speaking necessary, since the secondary slots
		/// are assigned based on slot number and epoch randomness. But including
		/// it makes things easier for higher-level users of the chain data to
		/// be aware of the author of a secondary-slot block.
		authority_index: super::AuthorityIndex,
		/// Slot number
		slot_number: SlotNumber,
	},
}

#[cfg(feature = "std")]
/// A BABE pre-runtime digest for std.
pub type PreDigest = RawPreDigest<schnorrkel::VRFOutput, schnorrkel::VRFProof>;

impl<VRFOutput, VRFProof> RawPreDigest<VRFOutput, VRFProof> {
	/// Returns the slot number of the pre digest.
	pub fn authority_index(&self) -> AuthorityIndex {
		match self {
			RawPreDigest::Primary { authority_index, .. } => *authority_index,
			RawPreDigest::Secondary { authority_index, .. } => *authority_index,
		}
	}

	/// Returns the slot number of the pre digest.
	pub fn slot_number(&self) -> SlotNumber {
		match self {
			RawPreDigest::Primary { slot_number, .. } => *slot_number,
			RawPreDigest::Secondary { slot_number, .. } => *slot_number,
		}
	}

	/// Returns the weight _added_ by this digest, not the cumulative weight
	/// of the chain.
	pub fn added_weight(&self) -> crate::BabeBlockWeight {
		match self {
			RawPreDigest::Primary { .. } => 1,
			RawPreDigest::Secondary { .. } => 0,
		}
	}
}

#[cfg(feature = "std")]
impl TryFrom<RawPreDigest> for PreDigest {
	type Error = SignatureError;

	fn try_from(raw: RawPreDigest) -> Result<PreDigest, SignatureError> {
		Ok(match raw {
			RawPreDigest::Primary { authority_index, slot_number, vrf_output, vrf_proof } =>
				RawPreDigest::Primary {
					authority_index,
					slot_number,
					vrf_output: vrf_output.try_into()?,
					vrf_proof: vrf_proof.try_into()?,
				},
			RawPreDigest::Secondary { authority_index, slot_number } =>
				RawPreDigest::Secondary {
					authority_index,
					slot_number,
				}
		})
	}
}

/// Information about the next epoch. This is broadcast in the first block
/// of the epoch.
#[derive(Decode, Encode, Default, PartialEq, Eq, Clone, sp_runtime::RuntimeDebug)]
pub struct NextEpochDescriptor {
	/// The authorities.
	pub authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,

	/// The value of randomness to use for the slot-assignment.
	pub randomness: Randomness,
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

	/// If this item is a BABE epoch, return it.
	fn as_next_epoch_descriptor(&self) -> Option<NextEpochDescriptor>;
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
}
