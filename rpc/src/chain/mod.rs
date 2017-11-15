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

impl<B> ChainApi for B where
	B: client::Blockchain + Send + Sync + 'static,
	B::Error: ::std::error::Error + Send,
{
	fn header(&self, hash: block::HeaderHash) -> Result<Option<block::Header>> {
		self.header(&hash).chain_err(|| "Blockchain error")
	}
}
