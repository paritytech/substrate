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

use super::error::Result;
use runtime_version::RuntimeVersion;
use rstd::vec::Vec;
use runtime_primitives::{traits::{Block as BlockT, Api}, generic::BlockId};
use primitives::AuthorityId;

/// Something that can be constructed to a runtime api.
pub trait ConstructRuntimeApi<Block: BlockT>: Sized {
	/// Construct the runtime api.
	fn construct_runtime_api<'a, T: CallApiAt<Block>>(call: &'a T) -> Api<'a, Self>;

	fn replace_call<'a, T: CallApiAt<Block>>(&self, new_call: &'a T);
}

/// Something that can call into the runtime.
pub trait CallApiAt<Block: BlockT> {
	/// Call the given API function with the given arguments and returns the result at the given
	/// block.
	fn call_api_at(
		&mut self,
		at: &BlockId<Block>,
		function: &'static str,
		args: Vec<u8>,
	) -> Result<Vec<u8>>;
}

/// The `Core` api trait that is mandantory for each runtime.
pub trait Core<Block: BlockT>: Send + Sync + ConstructRuntimeApi<Block> {
	/// Returns the version of the runtime.
	fn version(&self, at: &BlockId<Block>) -> Result<RuntimeVersion>;
	/// Returns the authorities.
	fn authorities(&self, at: &BlockId<Block>) -> Result<Vec<AuthorityId>>;
	/// Execute the given block.
	fn execute_block(&self, at: &BlockId<Block>, block: &Block) -> Result<()>;
	/// Initialise a block with the given header.
	fn initialise_block(
        &self,
        at: &BlockId<Block>,
        header: &<Block as BlockT>::Header
    ) -> Result<()>;
}

pub mod runtime {
	use super::*;

    /// The `Core` api trait that is mandantory for each runtime.
    pub trait Core<Block: BlockT> {
    	/// Returns the version of the runtime.
    	fn version() -> RuntimeVersion;
    	/// Returns the authorities.
    	fn authorities() -> Vec<AuthorityId>;
    	/// Execute the given block.
    	fn execute_block(block: Block);
    	/// Initialise a block with the given header.
    	fn initialise_block(header: <Block as BlockT>::Header);
    }
}
