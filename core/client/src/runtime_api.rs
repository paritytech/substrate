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

/// Traits for interfacing with the runtime from the client.

use error;
#[doc(hidden)]
pub use state_machine::OverlayedChanges;
pub use sr_api::*;
use runtime_primitives::traits::{Block as BlockT, Api};

/// Something that can be constructed to a runtime api.
pub trait ConstructRuntimeApi: Sized {
	type Block: BlockT;
	/// Construct the runtime api.
	fn construct_runtime_api<'a, T: CallIntoRuntime<Block=Self::Block>>(call: &'a T) -> Api<'a, Self>;
}

/// Something that can call into the runtime.
pub trait CallIntoRuntime {
	type Block: BlockT;

	/// Call the given API function with the given arguments and returns the result.
	fn call_api(
		&self,
		function: &'static str,
		args: Vec<u8>,
	) -> error::Result<Vec<u8>>;

	/// Call the given API function with the given arguments and returns the result at the given
	/// block.
	fn call_api_at(
		&self,
		at: &BlockId<Self::Block>,
		function: &'static str,
		args: Vec<u8>,
	) -> error::Result<Vec<u8>>;

	/// Call at the given state into the runtime.
	/// This is an auxiliary method, that is probably used by the implementation of `call_api` and
	/// `call_api_at`.
	fn call_at_state(
		&self,
		at: &BlockId<Self::Block>,
		function: &'static str,
		args: Vec<u8>,
		changes: &mut OverlayedChanges
	) -> error::Result<Vec<u8>>;
}
