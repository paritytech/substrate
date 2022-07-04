// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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
use super::{authorship, find_pre_digest, sassafras_err, BlockT, Epoch, Error};
use sc_consensus_slots::CheckedHeader;
use sp_consensus_sassafras::{
	digests::{CompatibleDigestItem, PreDigest},
	make_ticket_transcript, make_transcript, AuthorityId, AuthorityPair, AuthoritySignature,
	Ticket,
};
use sp_consensus_slots::Slot;
use sp_core::{ByteArray, Pair};
use sp_runtime::{traits::Header, DigestItem};

// Allowed slot drift.
const MAX_SLOT_DRIFT: u64 = 1;

/// Sassafras verification parameters
pub struct VerificationParams<'a, B: 'a + BlockT> {
	/// The header being verified.
	pub header: B::Header,
	/// The pre-digest of the header being verified.
	pub pre_digest: PreDigest,
	/// The slot number of the current time.
	pub slot_now: Slot,
	/// Epoch descriptor of the epoch this block _should_ be under, if it's valid.
	pub epoch: &'a Epoch,
	/// Expected ticket for this block.
	pub ticket: Option<Ticket>,
}

pub struct VerifiedHeaderInfo {
	pub pre_digest: DigestItem,
	pub seal: DigestItem,
	pub author: AuthorityId,
}

/// Check a header has been signed by the right key. If the slot is too far in
/// the future, an error will be returned. If successful, returns the pre-header
/// and the digest item containing the seal.
///
/// The seal must be the last digest. Otherwise, the whole header is considered
/// unsigned. This is required for security and must not be changed.
///
/// The given header can either be from a primary or secondary slot assignment,
/// with each having different validation logic.
pub fn check_header<B: BlockT + Sized>(
	params: VerificationParams<B>,
) -> Result<CheckedHeader<B::Header, VerifiedHeaderInfo>, Error<B>> {
	let VerificationParams { mut header, pre_digest, slot_now, epoch, ticket } = params;

	// Check that the slot is not in the future, with some drift being allowed.
	if pre_digest.slot > slot_now + MAX_SLOT_DRIFT {
		return Ok(CheckedHeader::Deferred(header, pre_digest.slot))
	}

	let author = match epoch.authorities.get(pre_digest.authority_index as usize) {
		Some(author) => author.0.clone(),
		None => return Err(sassafras_err(Error::SlotAuthorNotFound)),
	};

	// Check header signature

	let seal = header
		.digest_mut()
		.pop()
		.ok_or_else(|| sassafras_err(Error::HeaderUnsealed(header.hash())))?;

	let signature = seal
		.as_sassafras_seal()
		.ok_or_else(|| sassafras_err(Error::HeaderBadSeal(header.hash())))?;

	let pre_hash = header.hash();
	if !AuthorityPair::verify(&signature, &pre_hash, &author) {
		return Err(sassafras_err(Error::BadSignature(pre_hash)))
	}

	// Check authorship method and claim

	match (&ticket, &pre_digest.ticket_info) {
		(Some(ticket), Some(ticket_info)) => {
			log::debug!(target: "sassafras", "🌳 checking primary");
			if ticket_info.authority_index != pre_digest.authority_index {
				// TODO-SASS ... we can eventually remove auth index from ticket info
				log::error!(target: "sassafras", "🌳 Wrong primary authority index");
			}
			let transcript = make_ticket_transcript(
				&epoch.randomness,
				ticket_info.attempt as u64,
				epoch.epoch_index,
			);
			schnorrkel::PublicKey::from_bytes(author.as_slice())
				.and_then(|p| p.vrf_verify(transcript, &ticket, &ticket_info.proof))
				.map_err(|s| sassafras_err(Error::VRFVerificationFailed(s)))?;
		},
		(None, None) => {
			log::debug!(target: "sassafras", "🌳 checking secondary");
			let idx = authorship::secondary_authority_index(pre_digest.slot, params.epoch);
			if idx != pre_digest.authority_index as u64 {
				log::error!(target: "sassafras", "🌳 Wrong secondary authority index");
			}
		},
		(Some(_), None) => {
			log::warn!(target: "sassafras", "🌳 Unexpected secondary authoring mechanism");
			// TODO-SASS: maybe we can use a different error variant
			return Err(Error::UnexpectedAuthoringMechanism)
		},
		(None, Some(_)) => {
			log::warn!(target: "sassafras", "🌳 Unexpected primary authoring mechanism");
			// TODO-SASS: maybe we will use a different error variant
			return Err(Error::UnexpectedAuthoringMechanism)
		},
	}

	// Check block-vrf proof

	let transcript = make_transcript(&epoch.randomness, pre_digest.slot, epoch.epoch_index);
	schnorrkel::PublicKey::from_bytes(author.as_slice())
		.and_then(|p| {
			p.vrf_verify(transcript, &pre_digest.block_vrf_output, &pre_digest.block_vrf_proof)
		})
		.map_err(|s| sassafras_err(Error::VRFVerificationFailed(s)))?;

	let info = VerifiedHeaderInfo {
		pre_digest: CompatibleDigestItem::sassafras_pre_digest(pre_digest),
		seal,
		author,
	};

	Ok(CheckedHeader::Checked(header, info))
}
