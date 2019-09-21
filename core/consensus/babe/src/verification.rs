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

//! Verification for BABE headers.
use schnorrkel::vrf::{VRFOutput, VRFProof};
use sr_primitives::{DigestItem, traits::Header};
use primitives::{Pair, Public};
use babe_primitives::{Epoch, BabePreDigest, CompatibleDigestItem, BabeAuthorityWeight, AuthorityId};
use babe_primitives::{AuthoritySignature, SlotNumber, BabeBlockWeight, AuthorityIndex, AuthorityPair};
use slots::CheckedHeader;
use log::{debug, trace};
use super::{find_pre_digest, make_transcript, calculate_primary_threshold, check_primary_threshold};
use super::secondary_slot_author;

/// Check a header has been signed by the right key. If the slot is too far in
/// the future, an error will be returned. If successful, returns the pre-header
/// and the digest item containing the seal.
///
/// The seal must be the last digest.  Otherwise, the whole header is considered
/// unsigned.  This is required for security and must not be changed.
///
/// This digest item will always return `Some` when used with `as_babe_pre_digest`.
///
/// The given header can either be from a primary or secondary slot assignment,
/// with each having different validation logic.
pub(super) fn check_header<H: Header>(
	mut header: H,
	parent_header: H,
	slot_now: u64,
	epoch: &Epoch,
	c: (u64, u64),
) -> Result<CheckedHeader<H, (DigestItem<H::Hash>, DigestItem<H::Hash>)>, String> {
	trace!(target: "babe", "Checking header");
	let Epoch { authorities, randomness, epoch_index, secondary_slots, .. } = epoch;
	let seal = match header.digest_mut().pop() {
		Some(x) => x,
		None => return Err(format!("Header {:?} is unsealed", header.hash())),
	};

	let sig = seal.as_babe_seal().ok_or_else(|| {
		format!("Header {:?} has a bad seal", header.hash())
	})?;

	// the pre-hash of the header doesn't include the seal
	// and that's what we sign
	let pre_hash = header.hash();

	let pre_digest = find_pre_digest::<H>(&header)?;

	if pre_digest.slot_number() > slot_now {
		header.digest_mut().push(seal);
		return Ok(CheckedHeader::Deferred(header, pre_digest.slot_number()));
	}

	if pre_digest.authority_index() > authorities.len() as u32 {
		return Err(format!("Slot author not found"));
	}

	let parent_weight = {
		let parent_pre_digest = find_pre_digest::<H>(&parent_header)?;
		parent_pre_digest.weight()
	};

	match &pre_digest {
		BabePreDigest::Primary { vrf_output, vrf_proof, authority_index, slot_number, weight } => {
			debug!(target: "babe", "Verifying Primary block");

			let digest = (vrf_output, vrf_proof, *authority_index, *slot_number, *weight);

			check_primary_header::<H>(
				pre_hash,
				digest,
				sig,
				parent_weight,
				authorities,
				*randomness,
				*epoch_index,
				c,
			)?;
		},
		BabePreDigest::Secondary { authority_index, slot_number, weight } if *secondary_slots => {
			debug!(target: "babe", "Verifying Secondary block");

			let digest = (*authority_index, *slot_number, *weight);

			check_secondary_header::<H>(
				pre_hash,
				digest,
				sig,
				parent_weight,
				&authorities,
				*randomness,
			)?;
		},
		_ => {
			return Err(format!("Secondary slot assignments are disabled for the current epoch."));
		}
	}

	let pre_digest = CompatibleDigestItem::babe_pre_digest(pre_digest);
	Ok(CheckedHeader::Checked(header, (pre_digest, seal)))
}

/// Check a primary slot proposal header. We validate that the given header is
/// properly signed by the expected authority, and that the contained VRF proof
/// is valid. Additionally, the weight of this block must increase compared to
/// its parent since it is a primary block.
fn check_primary_header<H: Header>(
	pre_hash: H::Hash,
	pre_digest: (&VRFOutput, &VRFProof, AuthorityIndex, SlotNumber, BabeBlockWeight),
	signature: AuthoritySignature,
	parent_weight: BabeBlockWeight,
	authorities: &[(AuthorityId, BabeAuthorityWeight)],
	randomness: [u8; 32],
	epoch_index: u64,
	c: (u64, u64),
) -> Result<(), String> {
	let (vrf_output, vrf_proof, authority_index, slot_number, weight) = pre_digest;
	if weight != parent_weight + 1 {
		return Err("Invalid weight: should increase with Primary block.".into());
	}

	let author = &authorities[authority_index as usize].0;

	if AuthorityPair::verify(&signature, pre_hash, &author) {
		let (inout, _) = {
			let transcript = make_transcript(
				&randomness,
				slot_number,
				epoch_index,
			);

			schnorrkel::PublicKey::from_bytes(author.as_slice()).and_then(|p| {
				p.vrf_verify(transcript, vrf_output, vrf_proof)
			}).map_err(|s| {
				format!("VRF verification failed: {:?}", s)
			})?
		};

		let threshold = calculate_primary_threshold(c, authorities, authority_index as usize);
		if !check_primary_threshold(&inout, threshold) {
			return Err(format!("VRF verification of block by author {:?} failed: \
								  threshold {} exceeded", author, threshold));
		}

		Ok(())
	} else {
		Err(format!("Bad signature on {:?}", pre_hash))
	}
}

/// Check a secondary slot proposal header. We validate that the given header is
/// properly signed by the expected authority, which we have a deterministic way
/// of computing. Additionally, the weight of this block must stay the same
/// compared to its parent since it is a secondary block.
fn check_secondary_header<H: Header>(
	pre_hash: H::Hash,
	pre_digest: (AuthorityIndex, SlotNumber, BabeBlockWeight),
	signature: AuthoritySignature,
	parent_weight: BabeBlockWeight,
	authorities: &[(AuthorityId, BabeAuthorityWeight)],
	randomness: [u8; 32],
) -> Result<(), String> {
	let (authority_index, slot_number, weight) = pre_digest;

	if weight != parent_weight {
		return Err("Invalid weight: Should stay the same with secondary block.".into());
	}

	// check the signature is valid under the expected authority and
	// chain state.
	let expected_author = secondary_slot_author(
		slot_number,
		authorities,
		randomness,
	).ok_or_else(|| "No secondary author expected.".to_string())?;

	let author = &authorities[authority_index as usize].0;

	if expected_author != author {
		let msg = format!("Invalid author: Expected secondary author: {:?}, got: {:?}.",
			expected_author,
			author,
		);

		return Err(msg);
	}

	if AuthorityPair::verify(&signature, pre_hash.as_ref(), author) {
		Ok(())
	} else {
		Err(format!("Bad signature on {:?}", pre_hash))
	}
}
