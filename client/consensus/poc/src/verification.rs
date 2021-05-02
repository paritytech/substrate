// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// Copyright (C) 2021 Subspace Labs, Inc.
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
use super::{find_pre_digest, poc_err, BlockT, Epoch, Error};
use crate::{INITIAL_SOLUTION_RANGE, SALT};
use log::{debug, trace};
use sc_consensus_slots::CheckedHeader;
use schnorrkel::context::SigningContext;
use sp_consensus_poc::digests::{CompatibleDigestItem, PreDigest, Solution};
use sp_consensus_poc::FarmerSignature;
use sp_consensus_slots::Slot;
use sp_consensus_spartan::spartan::{self, Piece, Spartan};
use sp_core::Public;
use sp_runtime::{traits::DigestItemFor, traits::Header};
use std::convert::TryInto;

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
    /// Spartan instance
    pub(super) spartan: &'a Spartan,
    /// Signing context for verifying signatures
    pub(super) signing_context: &'a SigningContext,
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
) -> Result<CheckedHeader<B::Header, VerifiedHeaderInfo<B>>, Error<B>>
where
    DigestItemFor<B>: CompatibleDigestItem,
{
    let VerificationParams {
        mut header,
        pre_digest,
        slot_now,
        epoch,
        spartan,
        signing_context,
    } = params;

    let pre_digest = pre_digest
        .map(Ok)
        .unwrap_or_else(|| find_pre_digest::<B>(&header))?;

    trace!(target: "poc", "Checking header");
    let seal = match header.digest_mut().pop() {
        Some(x) => x,
        None => return Err(poc_err(Error::HeaderUnsealed(header.hash()))),
    };

    // TODO: Check if we need this signature and why do we have this and another one in `pre_digest`
    let sig = seal
        .as_poc_seal()
        .ok_or_else(|| poc_err(Error::HeaderBadSeal(header.hash())))?;

    if pre_digest.slot > slot_now {
        header.digest_mut().push(seal);
        return Ok(CheckedHeader::Deferred(header, pre_digest.slot));
    }

    debug!(target: "poc",
        "Verifying primary block #{} at slot: {}",
        header.number(),
        pre_digest.slot,
    );

    check_primary_header::<B>(
        &pre_digest,
        sig,
        &epoch,
        epoch.config.c,
        &spartan,
        &signing_context,
    )?;

    let info = VerifiedHeaderInfo {
        pre_digest: CompatibleDigestItem::poc_pre_digest(pre_digest),
        seal,
    };
    Ok(CheckedHeader::Checked(header, info))
}

pub(super) struct VerifiedHeaderInfo<B: BlockT> {
    pub(super) pre_digest: DigestItemFor<B>,
    pub(super) seal: DigestItemFor<B>,
}

/// Check a slot proposal header. We validate that the given header is
/// properly signed by the expected authority, and that the contained PoR proof
/// is valid.
fn check_primary_header<B: BlockT + Sized>(
    pre_digest: &PreDigest,
    _signature: FarmerSignature,
    epoch: &Epoch,
    _c: (u64, u64),
    spartan: &Spartan,
    signing_context: &SigningContext,
) -> Result<(), Error<B>> {
    if !is_within_solution_range(
        &pre_digest.solution,
        crate::create_challenge(epoch, pre_digest.slot),
        INITIAL_SOLUTION_RANGE,
    ) {
        return Err(Error::OutsideOfSolutionRange(pre_digest.slot));
    }

    let piece: Piece = pre_digest
        .solution
        .encoding
        .as_slice()
        .try_into()
        .map_err(|_error| Error::EncodingOfWrongSize)?;

    if !spartan::is_commitment_valid(&piece, &pre_digest.solution.tag, &SALT) {
        return Err(Error::InvalidCommitment(pre_digest.slot));
    }

    if !is_signature_valid(signing_context, &pre_digest.solution) {
        return Err(Error::BadSignature);
    }

    if !spartan.is_encoding_valid(
        piece,
        pre_digest.solution.public_key.as_ref(),
        pre_digest.solution.nonce,
    ) {
        return Err(Error::InvalidEncoding(pre_digest.slot));
    }

    // TODO: Other verification?

    Ok(())
}

fn is_within_solution_range(solution: &Solution, challenge: [u8; 8], solution_range: u64) -> bool {
    let target = u64::from_be_bytes(challenge);
    let tag = u64::from_be_bytes(solution.tag);

    let (lower, is_lower_overflowed) = target.overflowing_sub(solution_range / 2);
    let (upper, is_upper_overflowed) = target.overflowing_add(solution_range / 2);
    if is_lower_overflowed || is_upper_overflowed {
        upper <= tag || tag <= lower
    } else {
        lower <= tag && tag <= upper
    }
}

fn is_signature_valid(signing_context: &SigningContext, solution: &Solution) -> bool {
    let public_key = match schnorrkel::PublicKey::from_bytes(solution.public_key.as_slice()) {
        Ok(public_key) => public_key,
        Err(_) => {
            return false;
        }
    };
    let signature = match schnorrkel::Signature::from_bytes(&solution.signature) {
        Ok(signature) => signature,
        Err(_) => {
            return false;
        }
    };
    public_key
        .verify(signing_context.bytes(&solution.tag), &signature)
        .is_ok()
}
