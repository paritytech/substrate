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
use super::{find_pre_digest, sassafras_err, BlockT, Epoch, Error};
use sc_consensus_slots::CheckedHeader;
use sp_consensus_sassafras::{
	digests::{CompatibleDigestItem, PreDigest},
	make_transcript, AuthorityId, AuthorityPair, AuthoritySignature,
};
use sp_consensus_slots::Slot;
use sp_runtime::{traits::Header, DigestItem};

/// Sassafras verification parameters
pub struct VerificationParams<'a, B: 'a + BlockT> {
	/// The header being verified.
	pub header: B::Header,
	/// The pre-digest of the header being verified. This is optional - if prior verification
	/// code had to read it, it can be included here to avoid duplicate work.
	pub pre_digest: Option<PreDigest>,
	/// The slot number of the current time.
	pub slot_now: Slot,
	/// Epoch descriptor of the epoch this block _should_ be under, if it's valid.
	pub epoch: &'a Epoch,
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

	let pre_digest = pre_digest.map(Ok).unwrap_or_else(|| find_pre_digest::<B>(&header))?;

	if pre_digest.slot > slot_now {
		return Ok(CheckedHeader::Deferred(header, pre_digest.slot))
	}

	let seal = header
		.digest_mut()
		.pop()
		.ok_or_else(|| sassafras_err(Error::HeaderUnsealed(header.hash())))?;

	let _sig = seal
		.as_sassafras_seal()
		.ok_or_else(|| sassafras_err(Error::HeaderBadSeal(header.hash())))?;

	// The pre-hash of the header doesn't include the seal and that's what we sign
	let _pre_hash = header.hash();

	//let authorities = &epoch.authorities;
	let author = match epoch.authorities.get(pre_digest.authority_index as usize) {
		Some(author) => author.0.clone(),
		None => return Err(sassafras_err(Error::SlotAuthorNotFound)),
	};

	match pre_digest.ticket_vrf_proof {
		Some(_) => {
			// TODO-SASS: check primary
			// 1. the ticket proof is valid
			// 2. the block vrf proof is valid
			log::debug!(target: "sassafras", "🌳 checking primary (TODO)");
		},
		None => {
			// TODO-SASS: check secondary
			// 1. the expected author index
			log::debug!(target: "sassafras", "🌳 checking secondary (TODO)");
		},
	}

	let info = VerifiedHeaderInfo {
		pre_digest: CompatibleDigestItem::sassafras_pre_digest(pre_digest),
		seal,
		author,
	};

	Ok(CheckedHeader::Checked(header, info))
}
