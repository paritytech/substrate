// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

/// Re-export of parent module scope storage prefix.
pub use sp_core::offchain::STORAGE_PREFIX as STORAGE_PREFIX;

sp_api::decl_runtime_apis! {
	/// The offchain worker api.
	#[api_version(2)]
	pub trait OffchainWorkerApi {
		/// Starts the off-chain task for given block number.
		#[skip_initialize_block]
		#[changed_in(2)]
		fn offchain_worker(number: sp_runtime::traits::NumberFor<Block>);

		/// Starts the off-chain task for given block header.
		#[skip_initialize_block]
		fn offchain_worker(header: &Block::Header);
	}
}
