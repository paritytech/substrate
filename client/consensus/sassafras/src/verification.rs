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

//! Verification for Sassafras headers.
use sp_core::crypto::Pair;
use sp_runtime::traits::{Header as HeaderT, DigestItemFor};
use sp_consensus_sassafras::{
	SlotNumber, AuthorityId, AuthorityPair, AuthoritySignature,
};
use sp_consensus_sassafras::digests::{
	PreDigest, CompatibleDigestItem, PrimaryPreDigest, SecondaryPreDigest,
};
use sc_consensus_slots::CheckedHeader;
use log::{trace, debug};
use super::{Epoch, BlockT, Error, find_pre_digest};

/// Sassafras verification parameters
pub(super) struct VerificationParams<'a, B: 'a + BlockT> {
	/// the header being verified.
	pub(super) header: B::Header,
	/// the pre-digest of the header being verified. this is optional - if prior
	/// verification code had to read it, it can be included here to avoid duplicate
	/// work.
	pub(super) pre_digest: Option<PreDigest>,
	/// the slot number of the current time.
	pub(super) slot_now: SlotNumber,
	/// epoch descriptor of the epoch this block _should_ be under, if it's valid.
	pub(super) epoch: &'a Epoch,
	/// genesis config of this Sassafras chain.
	pub(super) config: &'a super::Config,
}

/// Check a header has been signed by the right key. If the slot is too far in
/// the future, an error will be returned. If successful, returns the pre-header
/// and the digest item containing the seal.
///
/// The seal must be the last digest.  Otherwise, the whole header is considered
/// unsigned.  This is required for security and must not be changed.
///
/// This digest item will always return `Some` when used with `as_sassafras_pre_digest`.
///
/// The given header can either be from a primary or secondary slot assignment,
/// with each having different validation logic.
pub(super) fn check_header<B: BlockT + Sized>(
	params: VerificationParams<B>,
) -> Result<CheckedHeader<B::Header, VerifiedHeaderInfo<B>>, Error<B>> where
	DigestItemFor<B>: CompatibleDigestItem,
{
	let VerificationParams {
		mut header,
		pre_digest,
		slot_now,
		epoch,
		config,
	} = params;

	let authorities = &epoch.validating.authorities;
	let pre_digest = pre_digest.map(Ok).unwrap_or_else(|| find_pre_digest::<B>(&header))?;

	trace!(target: "babe", "Checking header");
	let seal = match header.digest_mut().pop() {
		Some(x) => x,
		None => return Err(Error::HeaderUnsealed(header.hash())),
	};

	let sig = seal.as_sassafras_seal().ok_or_else(|| Error::HeaderBadSeal(header.hash()))?;

	// the pre-hash of the header doesn't include the seal
	// and that's what we sign
	let pre_hash = header.hash();

	if pre_digest.slot_number() > slot_now {
		header.digest_mut().push(seal);
		return Ok(CheckedHeader::Deferred(header, pre_digest.slot_number()));
	}

	let author = match authorities.get(pre_digest.authority_index() as usize) {
		Some(author) => author.0.clone(),
		None => return Err(Error::SlotAuthorNotFound),
	};

	match &pre_digest {
		PreDigest::Primary { .. } => {
			debug!(target: "sassafras", "Verifying Primary block");

			unimplemented!()
		},
		PreDigest::Secondary(digest) if config.secondary_slots => {
			debug!(target: "sassafras", "Verifying Secondary block");

			check_secondary_header::<B>(
				pre_hash,
				digest,
				sig,
				&epoch,
			)?;
		},
		_ => {
			return Err(Error::SecondarySlotAssignmentsDisabled);
		}
	}

	let info = VerifiedHeaderInfo {
		pre_digest: CompatibleDigestItem::sassafras_pre_digest(pre_digest),
		seal,
		author,
	};
	Ok(CheckedHeader::Checked(header, info))
}

pub(super) struct VerifiedHeaderInfo<B: BlockT> {
	pub(super) pre_digest: DigestItemFor<B>,
	pub(super) seal: DigestItemFor<B>,
	pub(super) author: AuthorityId,
}

/// Check a primary slot proposal header.
fn check_primary_header<B: BlockT + Sized>(
	pre_hash: B::Hash,
	pre_digest: &PrimaryPreDigest,
	signature: AuthoritySignature,
	epoch: &Epoch,
) -> Result<(), Error<B>> {
	unimplemented!()
}

/// Check a secondary slot proposal header. We validate that the given header is
/// properly signed by the expected authority, which we have a deterministic way
/// of computing. Additionally, the weight of this block must stay the same
/// compared to its parent since it is a secondary block.
fn check_secondary_header<B: BlockT>(
	pre_hash: B::Hash,
	pre_digest: &SecondaryPreDigest,
	signature: AuthoritySignature,
	epoch: &Epoch,
) -> Result<(), Error<B>> {
	// check the signature is valid under the expected authority and
	// chain state.
	let expected_author = super::authorship::secondary_slot_author(
		pre_digest.slot_number,
		&epoch.validating.authorities,
		epoch.validating.randomness,
	).ok_or_else(|| Error::NoSecondaryAuthorExpected)?;

	let author = &epoch.validating.authorities[pre_digest.authority_index as usize].0;

	if expected_author != author {
		return Err(Error::InvalidAuthor(expected_author.clone(), author.clone()));
	}

	if AuthorityPair::verify(&signature, pre_hash.as_ref(), author) {
		Ok(())
	} else {
		Err(Error::BadSignature(pre_hash))
	}
}
