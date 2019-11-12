// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Substrate client interfaces.

// TODO: make internal
pub mod error;
pub mod backend;
pub mod blockchain;
pub mod light;
pub mod notifications;
pub mod call_executor;
pub mod client;
pub mod offchain;

pub use error::*;
pub use backend::*;
pub use blockchain::*;
pub use light::*;
pub use notifications::*;
pub use call_executor::*;
pub use offchain::*;
pub use client::*;

pub use state_machine::{StorageProof, ExecutionStrategy};


/// Utility methods for the client.
pub mod utils {
    use super::HeaderBackend;
    use header_metadata::HeaderMetadata;
	use crate::error;
    use primitives::H256;
	use sr_primitives::traits::{Block as BlockT};
	use std::borrow::Borrow;

	/// Returns a function for checking block ancestry, the returned function will
	/// return `true` if the given hash (second parameter) is a descendent of the
	/// base (first parameter). If the `current` parameter is defined, it should
	/// represent the current block `hash` and its `parent hash`, if given the
	/// function that's returned will assume that `hash` isn't part of the local DB
	/// yet, and all searches in the DB will instead reference the parent.
	pub fn is_descendent_of<'a, Block: BlockT<Hash=H256>, T, H: Borrow<H256> + 'a>(
		client: &'a T,
		current: Option<(H, H)>,
	) -> impl Fn(&H256, &H256) -> Result<bool, error::Error> + 'a
		where T: HeaderBackend<Block> + HeaderMetadata<Block, Error=error::Error>,
	{
		move |base, hash| {
			if base == hash { return Ok(false); }

			let current = current.as_ref().map(|(c, p)| (c.borrow(), p.borrow()));

			let mut hash = hash;
			if let Some((current_hash, current_parent_hash)) = current {
				if base == current_hash { return Ok(false); }
				if hash == current_hash {
					if base == current_parent_hash {
						return Ok(true);
					} else {
						hash = current_parent_hash;
					}
				}
			}

			let ancestor = header_metadata::lowest_common_ancestor(client, *hash, *base)?;

			Ok(ancestor.hash == *base)
		}
	}
}
