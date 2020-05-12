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

//! BABE authority selection and slot claiming.

use sp_consensus_babe::{
	make_transcript, AuthorityId, BabeAuthorityWeight, BABE_VRF_PREFIX,
	SlotNumber, AuthorityPair,
};
use sp_consensus_babe::digests::{
	PreDigest, PrimaryPreDigest, SecondaryPlainPreDigest, SecondaryVRFPreDigest,
};
use sp_consensus_vrf::schnorrkel::{VRFOutput, VRFProof};
use sp_core::{U256, blake2_256};
use codec::Encode;
use schnorrkel::vrf::VRFInOut;
use sp_core::Pair;
use sc_keystore::KeyStorePtr;
use super::Epoch;

/// Calculates the primary selection threshold for a given authority, taking
/// into account `c` (`1 - c` represents the probability of a slot being empty).
pub(super) fn calculate_primary_threshold(
	c: (u64, u64),
	authorities: &[(AuthorityId, BabeAuthorityWeight)],
	authority_index: usize,
) -> u128 {
	use num_bigint::BigUint;
	use num_rational::BigRational;
	use num_traits::{cast::ToPrimitive, identities::One};

	let c = c.0 as f64 / c.1 as f64;

	let theta =
		authorities[authority_index].1 as f64 /
		authorities.iter().map(|(_, weight)| weight).sum::<u64>() as f64;

	assert!(theta > 0.0, "authority with weight 0.");

	// NOTE: in the equation `p = 1 - (1 - c)^theta` the value of `p` is always
	// capped by `c`. For all pratical purposes `c` should always be set to a
	// value < 0.5, as such in the computations below we should never be near
	// edge cases like `0.999999`.

	let p = BigRational::from_float(1f64 - (1f64 - c).powf(theta)).expect(
		"returns None when the given value is not finite; \
		 c is a configuration parameter defined in (0, 1]; \
		 theta must be > 0 if the given authority's weight is > 0; \
		 theta represents the validator's relative weight defined in (0, 1]; \
		 powf will always return values in (0, 1] given both the \
		 base and exponent are in that domain; \
		 qed.",
	);

	let numer = p.numer().to_biguint().expect(
		"returns None when the given value is negative; \
		 p is defined as `1 - n` where n is defined in (0, 1]; \
		 p must be a value in [0, 1); \
		 qed."
	);

	let denom = p.denom().to_biguint().expect(
		"returns None when the given value is negative; \
		 p is defined as `1 - n` where n is defined in (0, 1]; \
		 p must be a value in [0, 1); \
		 qed."
	);

	((BigUint::one() << 128) * numer / denom).to_u128().expect(
		"returns None if the underlying value cannot be represented with 128 bits; \
		 we start with 2^128 which is one more than can be represented with 128 bits; \
		 we multiple by p which is defined in [0, 1); \
		 the result must be lower than 2^128 by at least one and thus representable with 128 bits; \
		 qed.",
	)
}

/// Returns true if the given VRF output is lower than the given threshold,
/// false otherwise.
pub(super) fn check_primary_threshold(inout: &VRFInOut, threshold: u128) -> bool {
	u128::from_le_bytes(inout.make_bytes::<[u8; 16]>(BABE_VRF_PREFIX)) < threshold
}

/// Get the expected secondary author for the given slot and with given
/// authorities. This should always assign the slot to some authority unless the
/// authorities list is empty.
pub(super) fn secondary_slot_author(
	slot_number: u64,
	authorities: &[(AuthorityId, BabeAuthorityWeight)],
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

/// Claim a secondary slot if it is our turn to propose, returning the
/// pre-digest to use when authoring the block, or `None` if it is not our turn
/// to propose.
fn claim_secondary_slot(
	slot_number: SlotNumber,
	epoch: &Epoch,
	key_pairs: &[(AuthorityPair, usize)],
	author_secondary_vrf: bool,
) -> Option<(PreDigest, AuthorityPair)> {
	let Epoch { authorities, randomness, epoch_index, .. } = epoch;

	if authorities.is_empty() {
		return None;
	}

	let expected_author = super::authorship::secondary_slot_author(
		slot_number,
		authorities,
		*randomness,
	)?;

	for (pair, authority_index) in key_pairs {
		if pair.public() == *expected_author {
			let pre_digest = if author_secondary_vrf {
				let transcript = super::authorship::make_transcript(
					randomness,
					slot_number,
					*epoch_index,
				);

				let s = get_keypair(&pair).vrf_sign(transcript);

				PreDigest::SecondaryVRF(SecondaryVRFPreDigest {
					slot_number,
					vrf_output: VRFOutput(s.0.to_output()),
					vrf_proof: VRFProof(s.1),
					authority_index: *authority_index as u32,
				})
			} else {
				PreDigest::SecondaryPlain(SecondaryPlainPreDigest {
					slot_number,
					authority_index: *authority_index as u32,
				})
			};

			return Some((pre_digest, pair.clone()));
		}
	}

	None
}

/// Tries to claim the given slot number. This method starts by trying to claim
/// a primary VRF based slot. If we are not able to claim it, then if we have
/// secondary slots enabled for the given epoch, we will fallback to trying to
/// claim a secondary slot.
pub fn claim_slot(
	slot_number: SlotNumber,
	epoch: &Epoch,
	keystore: &KeyStorePtr,
) -> Option<(PreDigest, AuthorityPair)> {
	let key_pairs = {
		let keystore = keystore.read();
		epoch.authorities.iter()
			.enumerate()
			.flat_map(|(i, a)| {
				keystore.key_pair::<AuthorityPair>(&a.0).ok().map(|kp| (kp, i))
			})
			.collect::<Vec<_>>()
	};
	claim_slot_using_key_pairs(slot_number, epoch, &key_pairs)
}

/// Like `claim_slot`, but allows passing an explicit set of key pairs. Useful if we intend
/// to make repeated calls for different slots using the same key pairs.
pub fn claim_slot_using_key_pairs(
	slot_number: SlotNumber,
	epoch: &Epoch,
	key_pairs: &[(AuthorityPair, usize)],
) -> Option<(PreDigest, AuthorityPair)> {
	claim_primary_slot(slot_number, epoch, epoch.config.c, &key_pairs)
		.or_else(|| {
			if epoch.config.allowed_slots.is_secondary_plain_slots_allowed() ||
				epoch.config.allowed_slots.is_secondary_vrf_slots_allowed()
			{
				claim_secondary_slot(
					slot_number,
					&epoch,
					&key_pairs,
					epoch.config.allowed_slots.is_secondary_vrf_slots_allowed(),
				)
			} else {
				None
			}
		})
}

fn get_keypair(q: &AuthorityPair) -> &schnorrkel::Keypair {
	use sp_core::crypto::IsWrappedBy;
	sp_core::sr25519::Pair::from_ref(q).as_ref()
}

/// Claim a primary slot if it is our turn.  Returns `None` if it is not our turn.
/// This hashes the slot number, epoch, genesis hash, and chain randomness into
/// the VRF.  If the VRF produces a value less than `threshold`, it is our turn,
/// so it returns `Some(_)`. Otherwise, it returns `None`.
fn claim_primary_slot(
	slot_number: SlotNumber,
	epoch: &Epoch,
	c: (u64, u64),
	key_pairs: &[(AuthorityPair, usize)],
) -> Option<(PreDigest, AuthorityPair)> {
	let Epoch { authorities, randomness, epoch_index, .. } = epoch;

	for (pair, authority_index) in key_pairs {
		let transcript = super::authorship::make_transcript(randomness, slot_number, *epoch_index);

		// Compute the threshold we will use.
		//
		// We already checked that authorities contains `key.public()`, so it can't
		// be empty.  Therefore, this division in `calculate_threshold` is safe.
		let threshold = super::authorship::calculate_primary_threshold(c, authorities, *authority_index);

		let pre_digest = get_keypair(pair)
			.vrf_sign_after_check(transcript, |inout| super::authorship::check_primary_threshold(inout, threshold))
			.map(|s| {
				PreDigest::Primary(PrimaryPreDigest {
					slot_number,
					vrf_output: VRFOutput(s.0.to_output()),
					vrf_proof: VRFProof(s.1),
					authority_index: *authority_index as u32,
				})
			});

		// early exit on first successful claim
		if let Some(pre_digest) = pre_digest {
			return Some((pre_digest, pair.clone()));
		}
	}

	None
}
