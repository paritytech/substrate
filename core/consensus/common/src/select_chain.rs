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

use crate::error::Error;
use runtime_primitives::traits::{Block as BlockT, NumberFor};


/// The SelectChain trait defines the strategy upon which the head is chosen
/// if multiple forks are present for an opaque definition of "best" in the 
/// specific chain build.
////
/// The Strategy can be customised for the two use cases of authoring new blocks
/// upon the best chain or which fork to finalise. Unless implemented differently
/// by default finalisation methods fall back to use authoring, so as a minimum
/// `_authoring`-functions must be implemented. 
///
/// Any particular user must make explicit, however, whether they intend to finalise
/// or author through the using the right function call, as these might differ in
/// some implemntations.
///
/// Non-deterministicly finalising chains may only use the `_authoring` functions.
pub trait SelectChain<Block: BlockT>: Sync + Send + Clone {

	/// Get all leaves of the chain: block hashes that have no children currently.
	/// Leaves that can never be finalized will not be returned.
	fn leaves(&self) -> Result<Vec<<Block as BlockT>::Hash>, Error>;

	/// Get best block header for authoring.
	fn best_block_header_for_authoring(&self) -> Result<<Block as BlockT>::Header, Error>;

	/// Get best block header for finalisation
	fn best_block_header_for_finalisation(&self) -> Result<<Block as BlockT>::Header, Error> {
		self.best_block_header_for_authoring()
	}

	/// Get the most recent block hash of the best chain that contain block
	/// with the given `target_hash` for authoring
	fn best_containing_for_authoring(
		&self,
		target_hash: <Block as BlockT>::Hash,
		maybe_max_number: Option<NumberFor<Block>>
	) -> Result<Option<<Block as BlockT>::Hash>, Error>;

	/// Get the most recent block hash of the best chain that contain block
	/// with the given `target_hash` for finalisation
	fn best_containing_for_finalisation(
		&self,
		target_hash: <Block as BlockT>::Hash,
		maybe_max_number: Option<NumberFor<Block>>
	) -> Result<Option<<Block as BlockT>::Hash>, Error> {
		self.best_containing_for_authoring(target_hash, maybe_max_number)
	}
}