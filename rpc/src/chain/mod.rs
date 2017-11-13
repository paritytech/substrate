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

mod error;
mod chain;

#[cfg(test)]
mod tests;

use self::error::Result;

pub use self::chain::Chain;

build_rpc_trait! {
	/// Polkadot blockchain API
	pub trait ChainApi {
		/// Get header of a relay chain block.
		#[rpc(name = "chain_getHeader")]
		fn header(&self, u64) -> Result<block::Header>;
	}
}
