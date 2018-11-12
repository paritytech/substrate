// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Substrate system API.

pub mod error;

#[cfg(test)]
mod tests;

use self::error::Result;

build_rpc_trait! {
	/// Substrate system RPC API
	pub trait SystemApi {
		/// Get the node's implementation name. Plain old string.
		#[rpc(name = "system_name")]
		fn system_name(&self) -> Result<String>;

		/// Get the node implementation's version. Should be a semver string.
		#[rpc(name = "system_version")]
		fn system_version(&self) -> Result<String>;

		/// Get the chain's type. Given as a string identifier.
		#[rpc(name = "system_chain")]
		fn system_chain(&self) -> Result<String>;

		/// Get a custom set of properties as a JSON object, defined in the chain spec.
		#[rpc(name = "system_properties")]
		fn system_properties(&self) -> Result<serde_json::map::Map<String, serde_json::Value>>;
	}
}
