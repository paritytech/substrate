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
use schnorrkel::vrf::{VRFOutput, VRFProof};
use sp_runtime::{traits::Header, traits::DigestItemFor};
use sp_core::{Pair, Public};
use sp_consensus_sassafras::{AuthoritySignature, SlotNumber, AuthorityIndex, AuthorityPair, AuthorityId};
use sp_consensus_sassafras::digests::{PreDigest, CompatibleDigestItem};
use sc_consensus_slots::CheckedHeader;
use log::{debug, trace};
use super::{find_pre_digest, Epoch, BlockT, Error};

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

	let info = VerifiedHeaderInfo {
		pre_digest: CompatibleDigestItem::sassafras_pre_digest(pre_digest),
		seal,
		author: Default::default(),
	};
	Ok(CheckedHeader::Checked(header, info))
}

pub(super) struct VerifiedHeaderInfo<B: BlockT> {
	pub(super) pre_digest: DigestItemFor<B>,
	pub(super) seal: DigestItemFor<B>,
	pub(super) author: AuthorityId,
}
