// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//! Block evaluation and evaluation errors.

use super::MAX_BLOCK_SIZE;

use parity_codec::Encode;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, As};
use error_chain::{error_chain, error_chain_processing, impl_error_chain_processed,
	impl_extract_backtrace, impl_error_chain_kind, bail};

type BlockNumber = u64;

error_chain! {
	errors {
		BadProposalFormat {
			description("Proposal provided not a block."),
			display("Proposal provided not a block."),
		}
		WrongParentHash(expected: String, got: String) {
			description("Proposal had wrong parent hash."),
			display("Proposal had wrong parent hash. Expected {:?}, got {:?}", expected, got),
		}
		WrongNumber(expected: BlockNumber, got: BlockNumber) {
			description("Proposal had wrong number."),
			display("Proposal had wrong number. Expected {}, got {}", expected, got),
		}
		ProposalTooLarge(size: usize) {
			description("Proposal exceeded the maximum size."),
			display(
				"Proposal exceeded the maximum size of {} by {} bytes.",
				MAX_BLOCK_SIZE, size.saturating_sub(MAX_BLOCK_SIZE)
			),
		}
	}
}

/// Attempt to evaluate a substrate block as a node block, returning error
/// upon any initial validity checks failing.
pub fn evaluate_initial<Block: BlockT>(
	proposal: &Block,
	parent_hash: &<Block as BlockT>::Hash,
	parent_number: <<Block as BlockT>::Header as HeaderT>::Number,
) -> Result<()> {

	let encoded = Encode::encode(proposal);
	let proposal = Block::decode(&mut &encoded[..])
		.ok_or_else(|| ErrorKind::BadProposalFormat)?;

	if encoded.len() > MAX_BLOCK_SIZE {
		bail!(ErrorKind::ProposalTooLarge(encoded.len()))
	}

	if *parent_hash != *proposal.header().parent_hash() {
		bail!(ErrorKind::WrongParentHash(
			format!("{:?}", *parent_hash),
			format!("{:?}", proposal.header().parent_hash())
		));
	}

	if parent_number.as_() + 1 != proposal.header().number().as_() {
		bail!(ErrorKind::WrongNumber(parent_number.as_() + 1, proposal.header().number().as_()));
	}

	Ok(())
}
