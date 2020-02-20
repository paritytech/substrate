// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! The block builder runtime api.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_runtime::{traits::Block as BlockT, ApplyExtrinsicResult};

use sp_inherents::{InherentData, CheckInherentsResult};

/// Definitions for supporting the older version of API: v3
///
/// These definitions are taken from the 2c58e30246a029b53d51e5b24c31974ac539ee8b git revision.
#[deprecated(note = "These definitions here are only for compatibility reasons")]
pub mod compatibility_v3 {
	use sp_runtime::{DispatchOutcome, transaction_validity};
	use codec::{Encode, Decode};

	#[derive(Eq, PartialEq, Clone, Copy, Decode, Encode, Debug)]
	pub enum ApplyError {
		NoPermission,
		BadState,
		Validity(transaction_validity::TransactionValidityError),
	}

	// `ApplyOutcome` was renamed to `DispatchOutcome` with the layout preserved.
	pub type ApplyResult = Result<DispatchOutcome, ApplyError>;
}

sp_api::decl_runtime_apis! {
	/// The `BlockBuilder` api trait that provides the required functionality for building a block.
	#[api_version(5)]
	pub trait BlockBuilder {
		/// Compatibility version of `apply_extrinsic` for v3.
		///
		/// Only the return type is changed.
		#[changed_in(4)]
		#[allow(deprecated)]
		fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic)
			-> self::compatibility_v3::ApplyResult;

		/// Apply the given extrinsic.
		///
		/// Returns an inclusion outcome which specifies if this extrinsic is included in
		/// this block or not.
		fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyExtrinsicResult;
		/// Apply the given extrinsic.
		///
		/// Same as `apply_extrinsic`, but skips signature verification.
		fn apply_trusted_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyExtrinsicResult;
		/// Finish the current block.
		#[renamed("finalise_block", 3)]
		fn finalize_block() -> <Block as BlockT>::Header;
		/// Generate inherent extrinsics. The inherent data will vary from chain to chain.
		fn inherent_extrinsics(
			inherent: InherentData,
		) -> sp_std::vec::Vec<<Block as BlockT>::Extrinsic>;
		/// Check that the inherents are valid. The inherent data will vary from chain to chain.
		fn check_inherents(block: Block, data: InherentData) -> CheckInherentsResult;
		/// Generate a random seed.
		fn random_seed() -> <Block as BlockT>::Hash;
	}
}
