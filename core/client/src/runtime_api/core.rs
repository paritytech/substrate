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

use runtime_version::RuntimeVersion;
use runtime_primitives::traits::Block as BlockT;
use primitives::AuthorityId;
use rstd::vec::Vec;

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
}
