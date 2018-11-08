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

use super::{ConstructRuntimeApi, ApiExt};
use runtime_version::RuntimeVersion;
use runtime_primitives::{traits::Block as BlockT, generic::BlockId};
use primitives::AuthorityId;
use error::Result;

/// The `Core` api trait that is mandantory for each runtime.
/// This is the side that should be implemented for the `RuntimeApi` that is used by the `Client`.
/// Any modifications at one of these two traits, needs to be done on the other one as well.
pub trait Core<Block: BlockT>: 'static + Send + Sync + ConstructRuntimeApi<Block> + ApiExt {
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
	/// This is the side that should be implemented for the `Runtime`.
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
