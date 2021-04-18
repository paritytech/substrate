// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// Copyright (C) 2021 Subpace Labs, Inc.
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

//! Verification for PoC headers.
use sp_runtime::{traits::Header, traits::DigestItemFor};
use sp_core::{Pair, Public};
use sp_consensus_poc::{make_transcript, FarmerSignature, FarmerId};
use sp_consensus_poc::digests::{
	PreDigest, CompatibleDigestItem
};
use sc_consensus_slots::CheckedHeader;
use sp_consensus_slots::Slot;
use log::{debug, trace};
use super::{find_pre_digest, poc_err, Epoch, BlockT, Error};
use super::authorship::{calculate_threshold, check_threshold};

/// PoC verification parameters
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
/// This digest item will always return `Some` when used with `as_poc_pre_digest`.
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
	} = params;

	let pre_digest = pre_digest.map(Ok).unwrap_or_else(|| find_pre_digest::<B>(&header))?;

	trace!(target: "poc", "Checking header");
	let seal = match header.digest_mut().pop() {
		Some(x) => x,
		None => return Err(poc_err(Error::HeaderUnsealed(header.hash()))),
	};

	let sig = seal.as_poc_seal().ok_or_else(|| {
		poc_err(Error::HeaderBadSeal(header.hash()))
	})?;

	// the pre-hash of the header doesn't include the seal
	// and that's what we sign
	let pre_hash = header.hash();

	if pre_digest.slot > slot_now {
		header.digest_mut().push(seal);
		return Ok(CheckedHeader::Deferred(header, pre_digest.slot));
	}

	debug!(target: "babe",
		"Verifying primary block #{} at slot: {}",
		header.number(),
		pre_digest.slot,
	);

	check_primary_header::<B>(
		pre_hash,
		&pre_digest,
		sig,
		&epoch,
		epoch.config.c,
	)?;

	let info = VerifiedHeaderInfo {
		pre_digest: CompatibleDigestItem::poc_pre_digest(pre_digest),
		seal,
		// TODO: Fix author
		author: Default::default(),
	};
	Ok(CheckedHeader::Checked(header, info))
}

pub(super) struct VerifiedHeaderInfo<B: BlockT> {
	pub(super) pre_digest: DigestItemFor<B>,
	pub(super) seal: DigestItemFor<B>,
	pub(super) author: FarmerId,
}

/// Check a primary slot proposal header. We validate that the given header is
/// properly signed by the expected authority, and that the contained VRF proof
/// is valid. Additionally, the weight of this block must increase compared to
/// its parent since it is a primary block.
fn check_primary_header<B: BlockT + Sized>(
	_pre_hash: B::Hash,
	_pre_digest: &PreDigest,
	_signature: FarmerSignature,
	_epoch: &Epoch,
	_c: (u64, u64),
) -> Result<(), Error<B>> {
	// let author = &epoch.authorities[pre_digest.authority_index as usize].0;
	//
	// if AuthorityPair::verify(&signature, pre_hash, &author) {
	// 	let (inout, _) = {
	// 		let transcript = make_transcript(
	// 			&epoch.randomness,
	// 			pre_digest.slot,
	// 			epoch.epoch_index,
	// 		);
	//
	// 		schnorrkel::PublicKey::from_bytes(author.as_slice()).and_then(|p| {
	// 			p.vrf_verify(transcript, &pre_digest.vrf_output, &pre_digest.vrf_proof)
	// 		}).map_err(|s| {
	// 			poc_err(Error::VRFVerificationFailed(s))
	// 		})?
	// 	};
	//
	// 	let threshold = calculate_threshold(
	// 		c,
	// 		&epoch.authorities,
	// 		pre_digest.authority_index as usize,
	// 	);
	//
	// 	if !check_threshold(&inout, threshold) {
	// 		return Err(poc_err(Error::VRFVerificationOfBlockFailed(author.clone(), threshold)));
	// 	}
	//
	// 	Ok(())
	// } else {
	// 	Err(poc_err(Error::BadSignature(pre_hash)))
	// }
	// TODO: Proper verification
	Ok(())
}
