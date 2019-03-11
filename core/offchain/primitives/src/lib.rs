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

//! The Offchain Worker runtime api primitives.

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

use client::decl_runtime_apis;
use runtime_primitives::traits::NumberFor;

decl_runtime_apis! {
	/// The offchain worker api.
	pub trait OffchainWorkerApi {
		/// Starts the off-chain task for given block number.
		fn offchain_worker(number: NumberFor<Block>);
	}
}
