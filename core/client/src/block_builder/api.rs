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

//! The runtime api for building blocks.

use runtime_primitives::{traits::Block as BlockT, ApplyResult};
use rstd::vec::Vec;

decl_runtime_apis! {
	/// The `BlockBuilder` api trait that provides required functions for building a block for a runtime.
	pub trait BlockBuilder<Block: BlockT> {
		/// The runtime api for building blocks./// Apply the given extrinsics.
		fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyResult;
		/// Finish the current block.
		fn finalise_block() -> <Block as BlockT>::Header;
		/// Generate inherent extrinsics.
		fn inherent_extrinsics<InherentExtrinsic, UncheckedExtrinsic>(
			inherent: InherentExtrinsic
		) -> Vec<UncheckedExtrinsic>;
		/// Check that the inherents are valid.
		fn check_inherents<InherentData, Error>(
			block: Block, data: InherentData
		) -> Result<(), Error>;
		/// Generate a random seed.
		fn random_seed() -> <Block as BlockT>::Hash;
	}
}
