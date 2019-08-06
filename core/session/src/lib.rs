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

//! Substrate core types around sessions.

#![cfg_attr(not(feature = "std"), no_std)]

use rstd::vec::Vec;

client::decl_runtime_apis! {
	/// Session keys runtime api.
	pub trait SessionKeys {
		/// Generate a set of session keys with optionally using the given seed.
		///
		/// The seed needs to be a valid `utf8` string.
		///
		/// Returns the concatenated SCALE encoded public keys.
		fn generate(seed: Option<Vec<u8>>) -> Vec<u8>;
	}
}