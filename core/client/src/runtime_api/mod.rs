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

//! All the functionality required for declaring and implementing runtime api's.
//! Core api's are also declared here.

#[doc(hidden)]
#[cfg(feature = "std")]
pub use state_machine::OverlayedChanges;
#[doc(hidden)]
pub use runtime_primitives::{traits::Block as BlockT, generic::BlockId};
#[cfg(feature = "std")]
use runtime_primitives::traits::ApiRef;
use runtime_version::ApiId;
#[doc(hidden)]
pub use rstd::slice;
#[cfg(feature = "std")]
use rstd::result;
#[doc(hidden)]
pub use codec::{Encode, Decode};
#[cfg(feature = "std")]
use error;

mod core;
#[macro_use]
mod macros;
mod traits;

/// Something that can be constructed to a runtime api.
#[cfg(feature = "std")]
pub trait ConstructRuntimeApi<Block: BlockT>: Sized {
	/// Construct an instance of the runtime api.
	fn construct_runtime_api<'a, T: CallApiAt<Block>>(call: &'a T) -> ApiRef<'a, Self>;
}

/// An extension for the `RuntimeApi`.
#[cfg(feature = "std")]
pub trait ApiExt {
	/// The given closure will be called with api instance. Inside the closure any api call is
	/// allowed. After doing the api call, the closure is allowed to map the `Result` to a
	/// different `Result` type. This can be important, as the internal data structure that keeps
	/// track of modifications to the storage, discards changes when the `Result` is an `Err`.
	/// On `Ok`, the structure commits the changes to an internal buffer.
	fn map_api_result<F: FnOnce(&Self) -> result::Result<R, E>, R, E>(
		&self,
		map_call: F
	) -> result::Result<R, E>;
}

/// Something that can call the runtime api at a given block.
#[cfg(feature = "std")]
pub trait CallApiAt<Block: BlockT> {
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
}

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

pub use self::core::*;
pub use self::traits::*;

/// The runtime apis that should be implemented for the `Runtime`.
pub mod runtime {
	pub use super::core::runtime::Core;
	pub use super::traits::runtime::*;
}
