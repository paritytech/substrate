// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Polkadot blockchain API.

use primitives::block;
use client;
use state_machine;

mod error;

#[cfg(test)]
mod tests;

use self::error::{Result, ResultExt};

build_rpc_trait! {
	/// Polkadot blockchain API
	pub trait ChainApi {
		/// Get header of a relay chain block.
		#[rpc(name = "chain_getHeader")]
		fn header(&self, block::HeaderHash) -> Result<Option<block::Header>>;
	}
}

impl<B, E> ChainApi for client::Client<B, E> where
	B: client::backend::Backend + Send + Sync + 'static,
	E: state_machine::CodeExecutor + Send + Sync + 'static,
	client::error::Error: From<<<B as client::backend::Backend>::State as state_machine::backend::Backend>::Error>,
{
	fn header(&self, hash: block::HeaderHash) -> Result<Option<block::Header>> {
		client::Client::header(self, &hash).chain_err(|| "Blockchain error")
	}
}
