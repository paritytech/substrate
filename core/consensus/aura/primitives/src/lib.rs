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

//! Primitives for Aura.

#![cfg_attr(not(feature = "std"), no_std)]

/// The ApiIds for Aura authorship API.
pub mod id {
	use substrate_client::runtime_api::ApiId;

	/// ApiId for the AuraApi trait.
	pub const AURA_API: ApiId = *b"aura_api";
}

/// Aura consensus environmental data. Useful for block-proposing code.
pub struct AuraConsensusData {
	/// The timestamp the block should be authored with.
	pub timestamp: u64,
	/// The slot number.
	pub slot: u64,
	/// The duration of the slot, in seconds.
	pub slot_duration: u64,
}

/// Runtime-APIs
pub mod api {
	use substrate_client::decl_runtime_apis;
	decl_runtime_apis! {
		/// API necessary for block authorship with aura.
		pub trait AuraApi {
			/// Return the slot duration in seconds for Aura.
			/// Currently, only the value provided by this type at genesis
			/// will be used.
			///
			/// Dynamic slot duration may be supported in the future.
			fn slot_duration() -> u64;
		}
	}
}
