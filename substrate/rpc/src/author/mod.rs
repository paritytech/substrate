// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Substrate block-author/full-node API.

use primitives::block::Extrinsic;

pub mod error;

#[cfg(test)]
mod tests;

use self::error::Result;

build_rpc_trait! {
	/// Substrate authoring RPC API
	pub trait AuthorApi {
		/// Submit extrinsic for inclusion in block.
		#[rpc(name = "author_submitExtrinsic")]
		fn submit_extrinsic(&self, Extrinsic) -> Result<()>;
	}
}
