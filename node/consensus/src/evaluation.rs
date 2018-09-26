// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Block evaluation and evaluation errors.

use super::MAX_TRANSACTIONS_SIZE;

use codec::{Decode, Encode};
use node_runtime::{Block as GenericBlock, CheckedBlock};
use node_primitives::{Hash, BlockNumber, Timestamp};
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, As};


error_chain! {
	errors {
		BadProposalFormat {
			description("Proposal provided not a block."),
			display("Proposal provided not a block."),
		}
		TimestampInFuture {
			description("Proposal had timestamp too far in the future."),
			display("Proposal had timestamp too far in the future."),
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
				MAX_TRANSACTIONS_SIZE, size.saturating_sub(MAX_TRANSACTIONS_SIZE)
			),
		}
	}
}

/// Attempt to evaluate a substrate block as a node block, returning error
/// upon any initial validity checks failing.
pub fn evaluate_initial<Block: BlockT, Hash>(
	proposal: &Block,
	now: Timestamp,
	parent_hash: &Hash,
	parent_number: <<Block as BlockT>::Header as HeaderT>::Number,
) -> Result<CheckedBlock>
where
	Hash: PartialEq<<<GenericBlock as BlockT>::Header as HeaderT>::Hash>,
	Hash: Into<self::Hash> + Clone,
{
	const MAX_TIMESTAMP_DRIFT: Timestamp = 60;

	let encoded = Encode::encode(proposal);
	let proposal = GenericBlock::decode(&mut &encoded[..])
		.and_then(|b| CheckedBlock::new(b).ok())
		.ok_or_else(|| ErrorKind::BadProposalFormat)?;

	let transactions_size = proposal.extrinsics.iter().fold(0, |a, tx| {
		a + Encode::encode(tx).len()
	});

	if transactions_size > MAX_TRANSACTIONS_SIZE {
		bail!(ErrorKind::ProposalTooLarge(transactions_size))
	}

	if *parent_hash != *proposal.header().parent_hash() {
		bail!(ErrorKind::WrongParentHash((*parent_hash).clone().into(), proposal.header.parent_hash));
	}

	if parent_number.as_() + 1 != *proposal.header().number() {
		bail!(ErrorKind::WrongNumber(parent_number.as_() + 1, proposal.header.number));
	}

	let block_timestamp = proposal.timestamp();

	// lenient maximum -- small drifts will just be delayed using a timer.
	if block_timestamp > now + MAX_TIMESTAMP_DRIFT {
		bail!(ErrorKind::TimestampInFuture)
	}

	Ok(proposal)
}
