
// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate Consensus Common.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Consensus Common is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Consensus Common.  If not, see <http://www.gnu.org/licenses/>.

use std::error::Error;
use runtime_primitives::traits::Block;

// Chain head Selection
pub trait SelectChain<B: Block> {
    type Error: Error;
	/// Get best block header.
	fn best_block_header(&self) -> Result<<B as Block>::Header, Self::Error>;
	/// Get all leaves of the chain: block hashes that have no children currently.
	/// Leaves that can never be finalized will not be returned.
	fn leaves(&self) -> Result<Vec<<B as Block>::Hash>, Self::Error>;
}
