// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Verification for BABE headers.
use crate::{
	authorship::{calculate_primary_threshold, secondary_slot_author},
	babe_err, find_pre_digest, BlockT, Epoch, Error, AUTHORING_SCORE_LENGTH,
	AUTHORING_SCORE_VRF_CONTEXT, LOG_TARGET,
};
use log::{debug, trace};
use sc_consensus_epochs::Epoch as EpochT;
use sc_consensus_slots::CheckedHeader;
use sp_consensus_babe::{
	digests::{
		CompatibleDigestItem, PreDigest, PrimaryPreDigest, SecondaryPlainPreDigest,
		SecondaryVRFPreDigest,
	},
	make_vrf_sign_data, AuthorityId, AuthorityPair, AuthoritySignature,
};
use sp_consensus_slots::Slot;
use sp_core::{
	crypto::{VrfPublic, Wraps},
	Pair,
};
use sp_runtime::{traits::Header, DigestItem};

/// BABE verification parameters
pub(super) struct VerificationParams<'a, B: 'a + BlockT> {
	/// The header being verified.
	pub(super) header: B::Header,
	/// The pre-digest of the header being verified. this is optional - if prior
	/// verification code had to read it, it can be included here to avoid duplicate
	/// work.
	pub(super) pre_digest: Option<PreDigest>,
	/// The slot number of the current time.
	pub(super) slot_now: Slot,
	/// Epoch descriptor of the epoch this block _should_ be under, if it's valid.
	pub(super) epoch: &'a Epoch,
}

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
pub(super) fn check_header<B: BlockT + Sized>(
	params: VerificationParams<B>,
) -> Result<CheckedHeader<B::Header, VerifiedHeaderInfo>, Error<B>> {
	let VerificationParams { mut header, pre_digest, slot_now, epoch } = params;

	let authorities = &epoch.authorities;
	let pre_digest = pre_digest.map(Ok).unwrap_or_else(|| find_pre_digest::<B>(&header))?;

	trace!(target: LOG_TARGET, "Checking header");
	let seal = header
		.digest_mut()
		.pop()
		.ok_or_else(|| babe_err(Error::HeaderUnsealed(header.hash())))?;

	let sig = seal
		.as_babe_seal()
		.ok_or_else(|| babe_err(Error::HeaderBadSeal(header.hash())))?;

	// the pre-hash of the header doesn't include the seal
	// and that's what we sign
	let pre_hash = header.hash();

	if pre_digest.slot() > slot_now {
		header.digest_mut().push(seal);
		return Ok(CheckedHeader::Deferred(header, pre_digest.slot()))
	}

	let author = match authorities.get(pre_digest.authority_index() as usize) {
		Some(author) => author.0.clone(),
		None => return Err(babe_err(Error::SlotAuthorNotFound)),
	};

	match &pre_digest {
		PreDigest::Primary(primary) => {
			debug!(
				target: LOG_TARGET,
				"Verifying primary block #{} at slot: {}",
				header.number(),
				primary.slot,
			);

			check_primary_header::<B>(pre_hash, primary, sig, epoch, epoch.config.c)?;
		},
		PreDigest::SecondaryPlain(secondary)
			if epoch.config.allowed_slots.is_secondary_plain_slots_allowed() =>
		{
			debug!(
				target: LOG_TARGET,
				"Verifying secondary plain block #{} at slot: {}",
				header.number(),
				secondary.slot,
			);

			check_secondary_plain_header::<B>(pre_hash, secondary, sig, epoch)?;
		},
		PreDigest::SecondaryVRF(secondary)
			if epoch.config.allowed_slots.is_secondary_vrf_slots_allowed() =>
		{
			debug!(
				target: LOG_TARGET,
				"Verifying secondary VRF block #{} at slot: {}",
				header.number(),
				secondary.slot,
			);

			check_secondary_vrf_header::<B>(pre_hash, secondary, sig, epoch)?;
		},
		_ => return Err(babe_err(Error::SecondarySlotAssignmentsDisabled)),
	}

	let info = VerifiedHeaderInfo {
		pre_digest: CompatibleDigestItem::babe_pre_digest(pre_digest),
		seal,
		author,
	};
	Ok(CheckedHeader::Checked(header, info))
}

pub(super) struct VerifiedHeaderInfo {
	pub(super) pre_digest: DigestItem,
	pub(super) seal: DigestItem,
	pub(super) author: AuthorityId,
}

/// Check a primary slot proposal header. We validate that the given header is
/// properly signed by the expected authority, and that the contained VRF proof
/// is valid. Additionally, the weight of this block must increase compared to
/// its parent since it is a primary block.
fn check_primary_header<B: BlockT + Sized>(
	pre_hash: B::Hash,
	pre_digest: &PrimaryPreDigest,
	signature: AuthoritySignature,
	epoch: &Epoch,
	c: (u64, u64),
) -> Result<(), Error<B>> {
	let authority_id = &epoch.authorities[pre_digest.authority_index as usize].0;
	let mut epoch_index = epoch.epoch_index;

	if epoch.end_slot() <= pre_digest.slot {
		// Slot doesn't strictly belong to this epoch, create a clone with fixed values.
		epoch_index = epoch.clone_for_slot(pre_digest.slot).epoch_index;
	}

	if !AuthorityPair::verify(&signature, pre_hash, authority_id) {
		return Err(babe_err(Error::BadSignature(pre_hash)))
	}

	let data = make_vrf_sign_data(&epoch.randomness, pre_digest.slot, epoch_index);

	if !authority_id.as_inner_ref().vrf_verify(&data, &pre_digest.vrf_signature) {
		return Err(babe_err(Error::VrfVerificationFailed))
	}

	let threshold =
		calculate_primary_threshold(c, &epoch.authorities, pre_digest.authority_index as usize);

	let score = authority_id
		.as_inner_ref()
		.make_bytes::<AUTHORING_SCORE_LENGTH>(
			AUTHORING_SCORE_VRF_CONTEXT,
			&data.as_ref(),
			&pre_digest.vrf_signature.output,
		)
		.map(u128::from_le_bytes)
		.map_err(|_| babe_err(Error::VrfVerificationFailed))?;

	if score >= threshold {
		return Err(babe_err(Error::VrfThresholdExceeded(threshold)))
	}

	Ok(())
}

/// Check a secondary slot proposal header. We validate that the given header is
/// properly signed by the expected authority, which we have a deterministic way
/// of computing. Additionally, the weight of this block must stay the same
/// compared to its parent since it is a secondary block.
fn check_secondary_plain_header<B: BlockT>(
	pre_hash: B::Hash,
	pre_digest: &SecondaryPlainPreDigest,
	signature: AuthoritySignature,
	epoch: &Epoch,
) -> Result<(), Error<B>> {
	// check the signature is valid under the expected authority and chain state.
	let expected_author =
		secondary_slot_author(pre_digest.slot, &epoch.authorities, epoch.randomness)
			.ok_or(Error::NoSecondaryAuthorExpected)?;

	let author = &epoch.authorities[pre_digest.authority_index as usize].0;

	if expected_author != author {
		return Err(Error::InvalidAuthor(expected_author.clone(), author.clone()))
	}

	if !AuthorityPair::verify(&signature, pre_hash.as_ref(), author) {
		return Err(Error::BadSignature(pre_hash))
	}

	Ok(())
}

/// Check a secondary VRF slot proposal header.
fn check_secondary_vrf_header<B: BlockT>(
	pre_hash: B::Hash,
	pre_digest: &SecondaryVRFPreDigest,
	signature: AuthoritySignature,
	epoch: &Epoch,
) -> Result<(), Error<B>> {
	// check the signature is valid under the expected authority and chain state.
	let expected_author =
		secondary_slot_author(pre_digest.slot, &epoch.authorities, epoch.randomness)
			.ok_or(Error::NoSecondaryAuthorExpected)?;

	let author = &epoch.authorities[pre_digest.authority_index as usize].0;

	if expected_author != author {
		return Err(Error::InvalidAuthor(expected_author.clone(), author.clone()))
	}

	let mut epoch_index = epoch.epoch_index;
	if epoch.end_slot() <= pre_digest.slot {
		// Slot doesn't strictly belong to this epoch, create a clone with fixed values.
		epoch_index = epoch.clone_for_slot(pre_digest.slot).epoch_index;
	}

	if !AuthorityPair::verify(&signature, pre_hash.as_ref(), author) {
		return Err(Error::BadSignature(pre_hash))
	}

	let data = make_vrf_sign_data(&epoch.randomness, pre_digest.slot, epoch_index);

	if !author.as_inner_ref().vrf_verify(&data, &pre_digest.vrf_signature) {
		return Err(Error::VrfVerificationFailed)
	}

	Ok(())
}
