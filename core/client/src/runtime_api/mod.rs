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

//! API's for interfacing with the runtime via native/wasm.

#[doc(hidden)]
pub use state_machine::OverlayedChanges;
#[doc(hidden)]
pub use runtime_primitives::{
	traits::{Block as BlockT, Header as HeaderT, ProvideRuntimeApi}, generic::BlockId,
	transaction_validity::TransactionValidity, ApplyResult
};
use runtime_version::ApiId;
use primitives::OpaqueMetadata;
#[doc(hidden)]
pub use std::slice;
#[doc(hidden)]
pub use codec::{Encode, Decode};

pub mod core;
#[macro_use]
mod macros;

/// The ApiIds for the various standard runtime APIs.
pub mod id {
	use super::ApiId;

	/// ApiId for the BlockBuilder trait.
	pub const BLOCK_BUILDER: ApiId = *b"blkbuild";

	/// ApiId for the TaggedTransactionQueue trait.
	pub const TAGGED_TRANSACTION_QUEUE: ApiId = *b"validatx";

	/// ApiId for the Metadata trait.
	pub const METADATA: ApiId = *b"metadata";
}

decl_apis! {
	/// The `Metadata` api trait that returns metadata for the runtime.
	pub trait Metadata {
		fn metadata() -> OpaqueMetadata;
	}

	/// The `TaggedTransactionQueue` api trait for interfering with the new transaction queue.
	pub trait TaggedTransactionQueue<Block: BlockT> {
		fn validate_transaction<TransactionValidity>(tx: <Block as BlockT>::Extrinsic) -> TransactionValidity;
	}

	/// The `BlockBuilder` api trait that provides required functions for building a block for a runtime.
	pub trait BlockBuilder<Block: BlockT> {
		/// Apply the given extrinsics.
		fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyResult;
		/// Finish the current block.
		fn finalise_block() -> <Block as BlockT>::Header;
		/// Generate inherent extrinsics.
		fn inherent_extrinsics<InherentExtrinsic, UncheckedExtrinsic>(inherent: InherentExtrinsic) -> Vec<UncheckedExtrinsic>;
		/// Check that the inherents are valid.
		fn check_inherents<InherentData, Error>(block: Block, data: InherentData) -> Result<(), Error>;
		/// Generate a random seed.
		fn random_seed() -> <Block as BlockT>::Hash;
	}
}
