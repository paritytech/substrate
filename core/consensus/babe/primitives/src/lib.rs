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

//! Primitives for BABE.
#![deny(warnings, unsafe_code, missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

use runtime_primitives::ConsensusEngineId;
use substrate_client::decl_runtime_apis;
use safety_primitives::AuthorEquivProof;
use parity_codec::{Encode, Decode};

/// The `ConsensusEngineId` of BABE.
pub const BABE_ENGINE_ID: ConsensusEngineId = [b'b', b'a', b'b', b'e'];

/// Configuration data used by the BABE consensus engine.
#[derive(Copy, Clone, Hash, PartialEq, Eq, Debug, Encode, Decode)]
pub struct BabeConfiguration {
	/// The slot duration in milliseconds for BABE. Currently, only
	/// the value provided by this type at genesis will be used.
	///
	/// Dynamic slot duration may be supported in the future.
	pub slot_duration: u64,

	/// The expected block time in milliseconds for BABE. Currently,
	/// only the value provided by this type at genesis will be used.
	///
	/// Dynamic expected block time may be supported in the future.
	pub expected_block_time: u64,

	/// The maximum permitted VRF output, or *threshold*, for BABE. Currently,
	/// only the value provided by this type at genesis will be used.
	///
	/// Dynamic thresholds may be supported in the future.
	pub threshold: u64,
}

#[cfg(feature = "std")]
impl slots::SlotData for BabeConfiguration {
	/// Return the slot duration in milliseconds for BABE. Currently, only
	/// the value provided by this type at genesis will be used.
	///
	/// Dynamic slot duration may be supported in the future.
	fn slot_duration(&self) -> u64 {
		self.slot_duration
	}

	const SLOT_KEY: &'static [u8] = b"babe_bootstrap_data";
}

decl_runtime_apis! {
	/// API necessary for block authorship with BABE.
	pub trait BabeApi {
		/// Return the configuration for BABE. Currently,
		/// only the value provided by this type at genesis will be used.
		///
		/// Dynamic configuration may be supported in the future.
		fn startup_data() -> BabeConfiguration;
	}
}

/// Represents an Babe equivocation proof.
#[derive(Debug, Clone, Encode, Decode)]
pub struct BabeEquivocationProof<H, S> {
	first_header: H,
	second_header: H,
	first_signature: S,
	second_signature: S,
}

impl<H, S> AuthorEquivProof<H, S> for BabeEquivocationProof<H, S>
where
	H: Clone,
	S: Clone,
{
	/// Create a new Babe equivocation proof.
	fn new(
		first_header: H,
		second_header: H,
		first_signature: S,
		second_signature: S,
	) -> Self {
		BabeEquivocationProof {
			first_header,
			second_header,
			first_signature,
			second_signature,
		}
	}

	/// Get the first header involved in the equivocation.
	fn first_header(&self) -> H {
		self.first_header.clone()
	}

	/// Get the second header involved in the equivocation.
	fn second_header(&self) -> H {
		self.second_header.clone()
	}

	fn first_signature(&self) -> S {
		self.first_signature.clone()
	}

	fn second_signature(&self) -> S {
		self.second_signature.clone()
	}
}
