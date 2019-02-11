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

//! The runtime api for building blocks.

use runtime_primitives::{traits::Block as BlockT, ApplyResult, RuntimeString};
use rstd::vec::Vec;
use sr_api_macros::decl_runtime_apis;
pub use inherents::{InherentData, CheckInherentsResult};
use parity_codec_derive::{Encode, Decode};

/// The old representation of the inherent data.
#[doc(hide)]
#[derive(Encode, Decode)]
pub struct OldInherentData {
	/// Current timestamp.
	pub timestamp: u64,
	/// Blank report.
	pub consensus: (),
	/// Aura expected slot. Can take any value during block construction.
	pub aura_expected_slot: u64,
}

impl OldInherentData {
	/// Create a new `BasicInherentData` instance.
	pub fn new(timestamp: u64, expected_slot: u64) -> Self {
		Self {
			timestamp,
			consensus: (),
			aura_expected_slot: expected_slot,
		}
	}
}

/// Error type used while checking inherents.
#[doc(hide)]
#[derive(Encode, PartialEq)]
#[cfg_attr(feature = "std", derive(Decode))]
pub enum OldCheckInherentError {
	/// The inherents are generally valid but a delay until the given timestamp
	/// is required.
	ValidAtTimestamp(u64),
	/// Some other error has occurred.
	Other(RuntimeString),
}

decl_runtime_apis! {
	/// The `BlockBuilder` api trait that provides required functions for building a block for a runtime.
	#[api_version(2)]
	pub trait BlockBuilder {
		/// Apply the given extrinsics.
		fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyResult;
		/// Finish the current block.
		fn finalise_block() -> <Block as BlockT>::Header;
		/// Generate inherent extrinsics. The inherent data will vary from chain to chain.
		fn inherent_extrinsics(inherent: InherentData) -> Vec<<Block as BlockT>::Extrinsic>;
		/// Check that the inherents are valid. The inherent data will vary from chain to chain.
		fn check_inherents(block: Block, data: InherentData) -> CheckInherentsResult;
		/// Check that the inherents are valid. The inherent data will vary from chain to chain.
		///
		/// Old version that is used by the CC network.
		#[changed_in(2)]
		fn check_inherents(block: Block, data: OldInherentData) -> ::std::result::Result<(), OldCheckInherentError>;
		/// Generate a random seed.
		fn random_seed() -> <Block as BlockT>::Hash;
	}
}
