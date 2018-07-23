// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Polkadot block evaluation and evaluation errors.

use super::MAX_TRANSACTIONS_SIZE;

use codec::{Decode, Encode};
use polkadot_runtime::{Block as PolkadotGenericBlock, CheckedBlock};
use polkadot_primitives::{Block, Hash, BlockNumber, Timestamp};
use polkadot_primitives::parachain::Id as ParaId;

error_chain! {
	links {
		PolkadotApi(::polkadot_api::Error, ::polkadot_api::ErrorKind);
	}

	errors {
		ProposalNotForPolkadot {
			description("Proposal provided not a Polkadot block."),
			display("Proposal provided not a Polkadot block."),
		}
		TimestampInFuture {
			description("Proposal had timestamp too far in the future."),
			display("Proposal had timestamp too far in the future."),
		}
		TooManyCandidates(expected: usize, got: usize) {
			description("Proposal included more candidates than is possible."),
			display("Proposal included {} candidates for {} parachains", got, expected),
		}
		ParachainOutOfOrder {
			description("Proposal included parachains out of order."),
			display("Proposal included parachains out of order."),
		}
		UnknownParachain(id: ParaId) {
			description("Proposal included unregistered parachain."),
			display("Proposal included unregistered parachain {:?}", id),
		}
		WrongParentHash(expected: Hash, got: Hash) {
			description("Proposal had wrong parent hash."),
			display("Proposal had wrong parent hash. Expected {:?}, got {:?}", expected, got),
		}
		WrongNumber(expected: BlockNumber, got: BlockNumber) {
			description("Proposal had wrong number."),
			display("Proposal had wrong number. Expected {:?}, got {:?}", expected, got),
		}
		ProposalTooLarge(size: usize) {
			description("Proposal exceeded the maximum size."),
			display(
				"Proposal exceeded the maximum size of {} by {} bytes.",
				MAX_TRANSACTIONS_SIZE, MAX_TRANSACTIONS_SIZE.saturating_sub(*size)
			),
		}
	}
}

/// Attempt to evaluate a substrate block as a polkadot block, returning error
/// upon any initial validity checks failing.
pub fn evaluate_initial(
	proposal: &Block,
	now: Timestamp,
	parent_hash: &Hash,
	parent_number: BlockNumber,
	active_parachains: &[ParaId],
) -> Result<CheckedBlock> {
	const MAX_TIMESTAMP_DRIFT: Timestamp = 60;

	let encoded = Encode::encode(proposal);
	let proposal = PolkadotGenericBlock::decode(&mut &encoded[..])
		.and_then(|b| CheckedBlock::new(b).ok())
		.ok_or_else(|| ErrorKind::ProposalNotForPolkadot)?;

	let transactions_size = proposal.extrinsics.iter().fold(0, |a, tx| {
		a + Encode::encode(tx).len()
	});

	if transactions_size > MAX_TRANSACTIONS_SIZE {
		bail!(ErrorKind::ProposalTooLarge(transactions_size))
	}

	if proposal.header.parent_hash != *parent_hash {
		bail!(ErrorKind::WrongParentHash(*parent_hash, proposal.header.parent_hash));
	}

	if proposal.header.number != parent_number + 1 {
		bail!(ErrorKind::WrongNumber(parent_number + 1, proposal.header.number));
	}

	let block_timestamp = proposal.timestamp();

	// lenient maximum -- small drifts will just be delayed using a timer.
	if block_timestamp > now + MAX_TIMESTAMP_DRIFT {
		bail!(ErrorKind::TimestampInFuture)
	}

	{
		let n_parachains = active_parachains.len();
		if proposal.parachain_heads().len() > n_parachains {
			bail!(ErrorKind::TooManyCandidates(n_parachains, proposal.parachain_heads().len()));
		}

		let mut last_id = None;
		let mut iter = active_parachains.iter();
		for head in proposal.parachain_heads() {
			// proposed heads must be ascending order by parachain ID without duplicate.
			if last_id.as_ref().map_or(false, |x| x >= &head.parachain_index) {
				bail!(ErrorKind::ParachainOutOfOrder);
			}

			if !iter.any(|x| x == &head.parachain_index) {
				// must be unknown since active parachains are always sorted.
				bail!(ErrorKind::UnknownParachain(head.parachain_index))
			}

			last_id = Some(head.parachain_index);
		}
	}

	Ok(proposal)
}
