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

//! All the functionality required for declaring and implementing runtime apis.

#[doc(hidden)]
#[cfg(feature = "std")]
pub use state_machine::OverlayedChanges;
#[doc(hidden)]
pub use runtime_primitives::{
	traits::{Block as BlockT, GetNodeBlockType, GetRuntimeBlockType, ApiRef, RuntimeApiInfo},
	generic::BlockId, transaction_validity::TransactionValidity
};
#[doc(hidden)]
pub use runtime_version::{ApiId, RuntimeVersion, ApisVec, create_apis_vec};
#[doc(hidden)]
pub use rstd::{slice, mem};
#[cfg(feature = "std")]
use rstd::result;
pub use codec::{Encode, Decode};
#[cfg(feature = "std")]
use error;
use rstd::vec::Vec;
use primitives::{AuthorityId, OpaqueMetadata};


/// Something that can be constructed to a runtime api.
#[cfg(feature = "std")]
pub trait ConstructRuntimeApi<Block: BlockT> {
	/// Construct an instance of the runtime api.
	fn construct_runtime_api<'a, T: CallRuntimeAt<Block>>(
		call: &'a T
	) -> ApiRef<'a, Self> where Self: Sized;
}

/// An extension for the `RuntimeApi`.
#[cfg(feature = "std")]
pub trait ApiExt<Block: BlockT> {
	/// The given closure will be called with api instance. Inside the closure any api call is
	/// allowed. After doing the api call, the closure is allowed to map the `Result` to a
	/// different `Result` type. This can be important, as the internal data structure that keeps
	/// track of modifications to the storage, discards changes when the `Result` is an `Err`.
	/// On `Ok`, the structure commits the changes to an internal buffer.
	fn map_api_result<F: FnOnce(&Self) -> result::Result<R, E>, R, E>(
		&self,
		map_call: F
	) -> result::Result<R, E> where Self: Sized;

	/// Checks if the given api is implemented and versions match.
	fn has_api<A: RuntimeApiInfo + ?Sized>(
		&self,
		at: &BlockId<Block>
	) -> error::Result<bool> where Self: Sized;
}

/// Something that can call into the runtime at a given block.
#[cfg(feature = "std")]
pub trait CallRuntimeAt<Block: BlockT> {
	/// Calls the given api function with the given encoded arguments at the given block
	/// and returns the encoded result.
	fn call_api_at(
		&self,
		at: &BlockId<Block>,
		function: &'static str,
		args: Vec<u8>,
		changes: &mut OverlayedChanges,
		initialised_block: &mut Option<BlockId<Block>>,
	) -> error::Result<Vec<u8>>;

	/// Returns the runtime version at the given block.
	fn runtime_version_at(&self, at: &BlockId<Block>) -> error::Result<RuntimeVersion>;
}

decl_runtime_apis! {
	/// The `Core` api trait that is mandantory for each runtime.
	#[core_trait]
	pub trait Core {
		/// Returns the version of the runtime.
		fn version() -> RuntimeVersion;
		/// Returns the authorities.
		fn authorities() -> Vec<AuthorityId>;
		/// Execute the given block.
		fn execute_block(block: Block);
		/// Initialise a block with the given header.
		fn initialise_block(header: <Block as BlockT>::Header);
	}

	/// The `Metadata` api trait that returns metadata for the runtime.
	pub trait Metadata {
		/// Returns the metadata of a runtime.
		fn metadata() -> OpaqueMetadata;
	}

	/// The `TaggedTransactionQueue` api trait for interfering with the new transaction queue.
	pub trait TaggedTransactionQueue {
		/// Validate the given transaction.
		fn validate_transaction(tx: <Block as BlockT>::Extrinsic) -> TransactionValidity;
	}
}
