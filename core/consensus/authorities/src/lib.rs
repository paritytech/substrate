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

//! Authorities API.

#![cfg_attr(not(feature = "std"), no_std)]

use substrate_client::decl_runtime_apis;
use runtime_primitives::traits::AuthorityIdFor;
use rstd::vec::Vec;

decl_runtime_apis! {
	/// Authorities API.
	pub trait AuthoritiesApi {
		/// Returns the authorities at the given block.
		fn authorities() -> Vec<AuthorityIdFor<Block>>;
	}
}
