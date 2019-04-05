
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
use runtime_primitives::traits::{Block, NumberFor};

/// The SelectChain trait defines the strategy upon which the head is chosen
/// if multiple forks are present for an opaque definition of "best" in the 
/// specific chain build.
////
/// The Strategy can be customised for the two use cases of authoring new blocks
/// upon the best chain or which fork to finalise or just the main methods
/// `best_block_header` and `best_containing` can be implemented if the same strategy
/// is being used.
pub trait SelectChain<B: Block> {
    /// The Error type returned in case the call didn't succeed
    type Error: Error;

	/// Get all leaves of the chain: block hashes that have no children currently.
	/// Leaves that can never be finalized will not be returned.
	fn leaves(&self) -> Result<Vec<<B as Block>::Hash>, Self::Error>;

	/// Get best block header.
	fn best_block_header(&self) -> Result<<B as Block>::Header, Self::Error>;

	/// Get best block header for authoring
	fn best_block_header_for_authoring(&self) -> Result<<B as Block>::Header, Self::Error> {
        self.best_block_header()
    }

	/// Get best block header for finalisation
	fn best_block_header_for_finalisation(&self) -> Result<<B as Block>::Header, Self::Error> {
        self.best_block_header()
    }

	/// Get the most recent block hash of the best chain that contain block
    /// with the given `target_hash`.
    fn best_containing(
        &self,
        target_hash: <B as Block>::Hash,
        maybe_max_number: Option<NumberFor<B>>
    ) -> Result<Option<<B as Block>::Hash>, Self::Error>;
	
	/// Get the most recent block hash of the best chain that contain block
    /// with the given `target_hash` for authoring
    fn best_containing_for_authoring(
        &self,
        target_hash: <B as Block>::Hash,
        maybe_max_number: Option<NumberFor<B>>
    ) -> Result<Option<<B as Block>::Hash>, Self::Error> {
        self.best_containing(target_hash, maybe_max_number)
    }
	/// Get the most recent block hash of the best chain that contain block
    /// with the given `target_hash` for finalisation
    fn best_containing_for_finalisation(
        &self,
        target_hash: <B as Block>::Hash,
        maybe_max_number: Option<NumberFor<B>>
    ) -> Result<Option<<B as Block>::Hash>, Self::Error> {
        self.best_containing(target_hash, maybe_max_number)
    }
}
