// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

use sr_primitives::{traits::Block as BlockT, ApplyResult};
use rstd::vec::Vec;
use sr_api_macros::decl_runtime_apis;
use codec::Decode;
pub use inherents::{InherentData, CheckInherentsResult};

/// Outcome of a valid extrinsic application. Capable of being sliced.
///
/// Deprecated and just present for compatibility reasons.
#[derive(Eq, PartialEq, Clone, Copy, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
#[repr(u8)]
pub enum ApplyOutcomeOld {
	/// Successful application (extrinsic reported no issue).
	Success = 0,
	/// Failed application (extrinsic was probably a no-op other than fees).
	Fail = 1,
}

/// Reason why an extrinsic couldn't be applied (i.e. invalid extrinsic).
///
/// Deprecated and just present for compatibility reasons.
#[derive(Eq, PartialEq, Clone, Copy, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
#[repr(u8)]
pub enum ApplyErrorOld {
	/// Bad signature.
	BadSignature = 0,
	/// Nonce too low.
	Stale = 1,
	/// Nonce too high.
	Future = 2,
	/// Sending account had too low a balance.
	CantPay = 3,
	/// Block is full, no more extrinsics can be applied.
	FullBlock = 255,
}

/// Result from attempt to apply an extrinsic.
#[deprecated(note="Use `ApplyResult` from `sr-primitives`.")]
pub type ApplyResultOld = Result<ApplyOutcomeOld, ApplyErrorOld>;

decl_runtime_apis! {
	/// The `BlockBuilder` api trait that provides required functions for building a block for a runtime.
	#[api_version(4)]
	pub trait BlockBuilder {
		/// Apply the given extrinsics.
		#[changed_in(4)]
		fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyResultOld;
		/// Apply the given extrinsics.
		fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyResult;
		/// Finish the current block.
		#[renamed("finalise_block", 3)]
		fn finalize_block() -> <Block as BlockT>::Header;
		/// Generate inherent extrinsics. The inherent data will vary from chain to chain.
		fn inherent_extrinsics(inherent: InherentData) -> Vec<<Block as BlockT>::Extrinsic>;
		/// Check that the inherents are valid. The inherent data will vary from chain to chain.
		fn check_inherents(block: Block, data: InherentData) -> CheckInherentsResult;
		/// Generate a random seed.
		fn random_seed() -> <Block as BlockT>::Hash;
	}
}
