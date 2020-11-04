// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Block evaluation and evaluation errors.

use super::MAX_BLOCK_SIZE;

use codec::Encode;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, One, CheckedConversion};

// This is just a best effort to encode the number. None indicated that it's too big to encode
// in a u128.
type BlockNumber = Option<u128>;

/// Result type alias.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Proposal provided not a block.
	#[error("Proposal provided not a block: decoding error: {0}")]
	BadProposalFormat(#[from] codec::Error),
	/// Proposal had wrong parent hash.
	#[error("Proposal had wrong parent hash. Expected {expected:?}, got {got:?}")]
	WrongParentHash { expected: String, got: String },
	/// Proposal had wrong number.
	#[error("Proposal had wrong number. Expected {expected:?}, got {got:?}")]
	WrongNumber { expected: BlockNumber, got: BlockNumber },
	/// Proposal exceeded the maximum size.
	#[error(
		"Proposal exceeded the maximum size of {} by {} bytes.",
		MAX_BLOCK_SIZE, .0.saturating_sub(MAX_BLOCK_SIZE)
	)]
	ProposalTooLarge(usize),
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
		.map_err(|e| Error::BadProposalFormat(e))?;

	if encoded.len() > MAX_BLOCK_SIZE {
		return Err(Error::ProposalTooLarge(encoded.len()))
	}

	if *parent_hash != *proposal.header().parent_hash() {
		return Err(Error::WrongParentHash {
			expected: format!("{:?}", *parent_hash),
			got: format!("{:?}", proposal.header().parent_hash())
		});
	}

	if parent_number + One::one() != *proposal.header().number() {
		return Err(Error::WrongNumber {
			expected: parent_number.checked_into::<u128>().map(|x| x + 1),
			got: (*proposal.header().number()).checked_into::<u128>(),
		});
	}

	Ok(())
}
