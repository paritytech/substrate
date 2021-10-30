// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#[doc(hidden)]
pub use crate::sp_runtime::traits::{Block as BlockT, Extrinsic};
#[doc(hidden)]
pub use crate::sp_std::vec::Vec;

pub use sp_inherents::{
	CheckInherentsResult, InherentData, InherentIdentifier, IsFatalError, MakeFatalError,
};

/// A pallet that provides or verifies an inherent extrinsic.
///
/// The pallet may provide the inherent, verify an inherent, or both provide and verify.
pub trait ProvideInherent {
	/// The call type of the pallet.
	type Call;
	/// The error returned by `check_inherent`.
	type Error: codec::Encode + IsFatalError;
	/// The inherent identifier used by this inherent.
	const INHERENT_IDENTIFIER: self::InherentIdentifier;

	/// Create an inherent out of the given `InherentData`.
	fn create_inherent(data: &InherentData) -> Option<Self::Call>;

	/// Determines whether this inherent is required in this block.
	///
	/// - `Ok(None)` indicates that this inherent is not required in this block. The default
	/// implementation returns this.
	///
	/// - `Ok(Some(e))` indicates that this inherent is required in this block. `construct_runtime!`
	/// will call this function from in its implementation of `fn check_extrinsics`.
	/// If the inherent is not present, it will return `e`.
	///
	/// - `Err(_)` indicates that this function failed and further operations should be aborted.
	///
	/// NOTE: If inherent is required then the runtime asserts that the block contains at least
	/// one inherent for which:
	/// * type is [`Self::Call`],
	/// * [`Self::is_inherent`] returns true.
	fn is_inherent_required(_: &InherentData) -> Result<Option<Self::Error>, Self::Error> {
		Ok(None)
	}

	/// Check whether the given inherent is valid. Checking the inherent is optional and can be
	/// omitted by using the default implementation.
	///
	/// When checking an inherent, the first parameter represents the inherent that is actually
	/// included in the block by its author. Whereas the second parameter represents the inherent
	/// data that the verifying node calculates.
	///
	/// NOTE: A block can contains multiple inherent.
	fn check_inherent(_: &Self::Call, _: &InherentData) -> Result<(), Self::Error> {
		Ok(())
	}

	/// Return whether the call is an inherent call.
	///
	/// NOTE: Signed extrinsics are not inherent, but signed extrinsic with the given call variant
	/// can be dispatched.
	///
	/// # Warning
	///
	/// In FRAME, inherent are enforced to be before other extrinsics, for this reason,
	/// pallets with unsigned transactions **must ensure** that no unsigned transaction call
	/// is an inherent call, when implementing `ValidateUnsigned::validate_unsigned`.
	/// Otherwise block producer can produce invalid blocks by including them after non inherent.
	fn is_inherent(call: &Self::Call) -> bool;
}
