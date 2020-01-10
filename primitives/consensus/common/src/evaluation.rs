// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

use super::MAX_BLOCK_SIZE;

use codec::Encode;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, One, CheckedConversion};

// This is just a best effort to encode the number. None indicated that it's too big to encode
// in a u128.
type BlockNumber = Option<u128>;

/// Result type alias.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type.
#[derive(Debug, derive_more::Display)]
pub enum Error {
	/// Proposal provided not a block.
	#[display(fmt="Proposal provided not a block: decoding error: {}", _0)]
	BadProposalFormat(codec::Error),
	/// Proposal had wrong parent hash.
	#[display(fmt="Proposal had wrong parent hash. Expected {:?}, got {:?}", expected, got)]
	WrongParentHash { expected: String, got: String },
	/// Proposal had wrong number.
	#[display(fmt="Proposal had wrong number. Expected {:?}, got {:?}", expected, got)]
	WrongNumber { expected: BlockNumber, got: BlockNumber },
	/// Proposal exceeded the maximum size.
	#[display(
		fmt="Proposal exceeded the maximum size of {} by {} bytes.",
		"MAX_BLOCK_SIZE", "_0.saturating_sub(MAX_BLOCK_SIZE)"
	)]
	ProposalTooLarge(usize),
}

impl std::error::Error for Error {}

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
