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

use rstd::prelude::*;
use codec::Slicable;
use polkadot_primitives::{Header, Block, UncheckedTransaction};

/// Execute a block.
pub fn execute_block(block: Block) {
	::runtime::system::internal::execute_block(block);
}

/// Execute a transaction. Input data is the concatenation of a serialized header and
/// transaction. Returns the new header.
pub fn execute_transaction((header, utx): (Header, UncheckedTransaction)) -> Header {
	::runtime::system::internal::execute_transaction(utx, header)
}

/// Finalize a block, given its header.
pub fn finalise_block(header: Header) -> Vec<u8> {
	let header = ::runtime::system::internal::finalise_block(header);
	header.to_vec()
}

/// Run whatever tests we have on a full block.
pub fn run_tests(block: Block) -> u32 {
	let stxs = block.transactions.iter().map(Slicable::to_vec).collect::<Vec<_>>();
	stxs.len() as u32
}

impl_stubs!(
	execute_block => execute_encoded_block,
	execute_transaction => execute_encoded_transaction,
	finalise_block => finalise_encoded_block,
	run_tests => run_encoded_block_tests
);
