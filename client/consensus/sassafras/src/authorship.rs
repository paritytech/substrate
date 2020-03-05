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

//! Sassafras authority selection and slot claiming.

use std::{hash::Hash, collections::HashMap};
use codec::Encode;
use merlin::Transcript;
use schnorrkel::vrf;
use sp_core::{blake2_256, U256, crypto::Pair};
use sp_api::NumberFor;
use sp_runtime::traits::Block as BlockT;
use sp_consensus_sassafras::{
	SlotNumber, AuthorityPair, SassafrasConfiguration, AuthorityId,
	SassafrasAuthorityWeight, SASSAFRAS_ENGINE_ID,
	VRFProof, SASSAFRAS_TICKET_VRF_PREFIX, VRFOutput,
	digests::{PreDigest, PrimaryPreDigest, SecondaryPreDigest},
};
use sc_consensus_epochs::ViableEpochDescriptor;
use sc_keystore::KeyStorePtr;
use log::trace;
use super::{Epoch, GeneratingSet, PendingProof};

/// Calculates the primary selection threshold for a given authority, taking
/// into account `c` (`1 - c` represents the probability of a slot being empty).
pub fn calculate_primary_threshold(
	c: (u64, u64),
	authorities: &[(AuthorityId, SassafrasAuthorityWeight)],
	authority_index: usize,
) -> u128 {
	use num_bigint::BigUint;
	use num_rational::BigRational;
	use num_traits::{cast::ToPrimitive, identities::One};

	let c = c.0 as f64 / c.1 as f64;

	let theta =
		authorities[authority_index].1 as f64 /
		authorities.iter().map(|(_, weight)| weight).sum::<u64>() as f64;

	let calc = || {
		let p = BigRational::from_float(1f64 - (1f64 - c).powf(theta))?;
		let numer = p.numer().to_biguint()?;
		let denom = p.denom().to_biguint()?;
		((BigUint::one() << 128) * numer / denom).to_u128()
	};

	calc().unwrap_or(u128::max_value())
}

/// Returns true if the given VRF output is lower than the given threshold,
/// false otherwise.
pub fn check_primary_threshold(inout: &vrf::VRFInOut, threshold: u128) -> bool {
	u128::from_le_bytes(inout.make_bytes::<[u8; 16]>(SASSAFRAS_TICKET_VRF_PREFIX)) < threshold
}

/// Tries to claim the given slot number. This method starts by trying to claim
/// a primary VRF based slot. If we are not able to claim it, then if we have
/// secondary slots enabled for the given epoch, we will fallback to trying to
/// claim a secondary slot.
pub(super) fn claim_slot(
	slot_number: SlotNumber,
	epoch: &Epoch,
	config: &SassafrasConfiguration,
	keystore: &KeyStorePtr,
) -> Option<(PreDigest, AuthorityPair)> {
	claim_primary_slot(slot_number, epoch, keystore).or_else(|| {
		if config.secondary_slots {
			claim_secondary_slot(
				slot_number,
				epoch,
				&epoch.validating.authorities,
				keystore,
				epoch.validating.randomness,
			)
		} else {
			None
		}
	})
}

const MAX_PRE_DIGEST_COMMITMENTS: usize = 4;

/// Claim a primary slot.
fn claim_primary_slot(
	slot_number: SlotNumber,
	epoch: &Epoch,
	keystore: &KeyStorePtr,
) -> Option<(PreDigest, AuthorityPair)> {
	let ticket_vrf_index = epoch.validating.proofs.iter().position(|(s, _)| *s == slot_number)? as u32;
	let ticket_vrf_proof = epoch.validating.proofs[ticket_vrf_index as usize].clone().1;
	let pending_index = epoch.validating.pending.iter()
		.position(|p| p.vrf_proof == ticket_vrf_proof)?;
	let ticket_vrf_attempt = epoch.validating.pending[pending_index].attempt;
	let authority_index = epoch.validating.pending[pending_index].authority_index;
	let ticket_vrf_output = epoch.validating.pending[pending_index].vrf_output.clone();

	let keystore = keystore.read();
	let pair = keystore.key_pair::<AuthorityPair>(
		&epoch.validating.authorities[authority_index as usize].0
	).ok()?;
	let post_transcript = make_post_transcript(
		&epoch.validating.randomness,
		slot_number,
		epoch.validating.epoch_index,
	);
	let (post_vrf_inout, post_vrf_proof, _) = get_keypair(&pair).vrf_sign(post_transcript);
	let post_vrf_output = VRFOutput(post_vrf_inout.to_output());
	let post_vrf_proof = VRFProof(post_vrf_proof);

	let mut commitments = Vec::new();
	for pending_proof in &epoch.publishing.pending {
		if commitments.len() < MAX_PRE_DIGEST_COMMITMENTS &&
			epoch.publishing.proofs.iter().position(|p| *p == pending_proof.vrf_proof).is_none()
		{
			commitments.push(pending_proof.vrf_proof.clone());
		}
	}
	trace!(target: "sassafras", "Appending commitment length: {}", commitments.len());

	let claim = PreDigest::Primary(PrimaryPreDigest {
		ticket_vrf_index, ticket_vrf_attempt, ticket_vrf_output,
		authority_index, slot_number, post_vrf_proof, post_vrf_output,
		commitments,
	});

	trace!(target: "sassafras", "Claimed a primary slot with slot number: {:?}", slot_number);
	trace!(target: "sassafras", "Epoch data as of now: {:?}", epoch);

	Some((claim, pair))
}

fn get_keypair(q: &AuthorityPair) -> &schnorrkel::Keypair {
	use sp_core::crypto::IsWrappedBy;
	sp_core::sr25519::Pair::from_ref(q).as_ref()
}

impl GeneratingSet {
	/// Get or generate pending proofs for current epoch, given keystore.
	pub fn append_to_pending(
		&mut self,
		keystore: &KeyStorePtr
	) {
		let keystore = keystore.read();

		for (pair, authority_index) in self.authorities.iter()
			.enumerate()
			.flat_map(|(i, a)| {
				keystore.key_pair::<AuthorityPair>(&a.0).ok().map(|kp| (kp, i))
			})
		{
			for attempt in 0..self.max_attempts() {
				let transcript = make_ticket_transcript(
					&self.randomness,
					attempt,
					self.epoch_index
				);

				let threshold = calculate_primary_threshold(
					self.threshold(),
					&self.authorities,
					authority_index
				);

				if let Some((inout, proof, _)) = get_keypair(&pair)
					.vrf_sign_after_check(transcript, |inout| {
						check_primary_threshold(inout, threshold)
					})
				{
					self.pending.push(PendingProof::new(
						attempt,
						authority_index as u32,
						self.authorities.len() as u32,
						VRFOutput(inout.to_output()),
						VRFProof(proof)
					));
				}
			}

		}
	}
}

/// Claim a secondary slot if it is our turn to propose, returning the
/// pre-digest to use when authoring the block, or `None` if it is not our turn
/// to propose.
fn claim_secondary_slot(
	slot_number: SlotNumber,
	epoch: &Epoch,
	authorities: &[(AuthorityId, SassafrasAuthorityWeight)],
	keystore: &KeyStorePtr,
	randomness: [u8; 32],
) -> Option<(PreDigest, AuthorityPair)> {
	if authorities.is_empty() {
		return None;
	}

	trace!(target: "sassafras", "Claiming a secondary slot with slot number: {:?}", slot_number);
	trace!(target: "sassafras", "Epoch data as of now: {:?}", epoch);

	let expected_author = secondary_slot_author(
		slot_number,
		authorities,
		randomness,
	)?;

	let keystore = keystore.read();

	for (pair, authority_index) in authorities.iter()
		.enumerate()
		.flat_map(|(i, a)| {
			keystore.key_pair::<AuthorityPair>(&a.0).ok().map(|kp| (kp, i))
		})
	{
		if pair.public() == *expected_author {
			let mut commitments = Vec::new();
			for pending_proof in &epoch.publishing.pending {
				if commitments.len() < MAX_PRE_DIGEST_COMMITMENTS && epoch.publishing.proofs.iter()
					.position(|p| *p == pending_proof.vrf_proof)
					.is_none()
				{
					commitments.push(pending_proof.vrf_proof.clone());
				}
			}
			trace!(target: "sassafras", "Appending commitment length: {}", commitments.len());

			let pre_digest = PreDigest::Secondary(SecondaryPreDigest {
				slot_number,
				authority_index: authority_index as u32,
				commitments,
			});

			return Some((pre_digest, pair));
		}
	}

	None
}

/// Get the expected secondary author for the given slot and with given
/// authorities. This should always assign the slot to some authority unless the
/// authorities list is empty.
pub(super) fn secondary_slot_author(
	slot_number: u64,
	authorities: &[(AuthorityId, SassafrasAuthorityWeight)],
	randomness: [u8; 32],
) -> Option<&AuthorityId> {
	if authorities.is_empty() {
		return None;
	}

	let rand = U256::from((randomness, slot_number).using_encoded(blake2_256));

	let authorities_len = U256::from(authorities.len());
	let idx = rand % authorities_len;

	let expected_author = authorities.get(idx.as_u32() as usize)
		.expect("authorities not empty; index constrained to list length; \
				this is a valid index; qed");

	Some(&expected_author.0)
}

#[allow(deprecated)]
pub fn make_ticket_transcript(
	randomness: &[u8],
	attempt: u64,
	epoch: u64,
) -> Transcript {
	let mut transcript = Transcript::new(&SASSAFRAS_ENGINE_ID);
	transcript.commit_bytes(b"type", b"ticket");
	transcript.commit_bytes(b"attempt", &attempt.to_le_bytes());
	transcript.commit_bytes(b"current epoch", &epoch.to_le_bytes());
	transcript.commit_bytes(b"chain randomness", randomness);
	transcript
}

#[allow(deprecated)]
pub fn make_post_transcript(
	randomness: &[u8],
	slot_number: u64,
	epoch: u64,
) -> Transcript {
	let mut transcript = Transcript::new(&SASSAFRAS_ENGINE_ID);
	transcript.commit_bytes(b"type", b"post");
	transcript.commit_bytes(b"slot number", &slot_number.to_le_bytes());
	transcript.commit_bytes(b"current epoch", &epoch.to_le_bytes());
	transcript.commit_bytes(b"chain randomness", randomness);
	transcript
}
