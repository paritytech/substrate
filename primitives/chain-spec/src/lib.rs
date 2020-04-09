// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Types and traits related to chain specifications.

/// The type of a chain.
///
/// This can be used by tools to determine the type of a chain for displaying
/// additional information or enabling additional features.
#[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq, Clone)]
pub enum ChainType {
	/// A development chain that runs mainly on one node.
	Development,
	/// A local chain that runs locally on multiple nodes for testing purposes.
	Local,
	/// A live chain.
	Live,
	/// Some custom chain type.
	Custom(String),
}

impl Default for ChainType {
	fn default() -> Self {
		Self::Live
	}
}

/// Arbitrary properties defined in chain spec as a JSON object
pub type Properties = serde_json::map::Map<String, serde_json::Value>;
