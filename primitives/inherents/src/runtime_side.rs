// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use crate::{InherentData, IsFatalError};

/// Auxiliary to make any given error resolve to `is_fatal_error() == true`.
#[derive(codec::Encode)]
pub struct MakeFatalError<E>(E);

impl<E: codec::Encode> From<E> for MakeFatalError<E> {
	fn from(err: E) -> Self {
		MakeFatalError(err)
	}
}

impl<E: codec::Encode> IsFatalError for MakeFatalError<E> {
	fn is_fatal_error(&self) -> bool {
		true
	}
}

/// A pallet that provides or verifies an inherent extrinsic.
///
/// The pallet may provide the inherent, verify an inherent, or both provide and verify.
pub trait ProvideInherent {
	/// The call type of the pallet.
	type Call;
	/// The error returned by `check_inherent`.
	type Error: codec::Encode + IsFatalError;
	/// The inherent identifier used by this inherent.
	const INHERENT_IDENTIFIER: crate::InherentIdentifier;

	/// Create an inherent out of the given `InherentData`.
	fn create_inherent(data: &InherentData) -> Option<Self::Call>;

	/// Determines whether this inherent is required in this block.
	///
	/// - `Ok(None)` indicates that this inherent is not required in this block. The default
	/// implementation returns this.
	///
	/// - `Ok(Some(e))` indicates that this inherent is required in this block. The
	/// `impl_outer_inherent!`, will call this function from its `check_extrinsics`.
	/// If the inherent is not present, it will return `e`.
	///
	/// - `Err(_)` indicates that this function failed and further operations should be aborted.
	///
	/// CAUTION: This check has a bug when used in pallets that also provide unsigned transactions.
	/// See <https://github.com/paritytech/substrate/issues/6243> for details.
	fn is_inherent_required(_: &InherentData) -> Result<Option<Self::Error>, Self::Error> { Ok(None) }

	/// Check whether the given inherent is valid. Checking the inherent is optional and can be
	/// omitted by using the default implementation.
	///
	/// When checking an inherent, the first parameter represents the inherent that is actually
	/// included in the block by its author. Whereas the second parameter represents the inherent
	/// data that the verifying node calculates.
	fn check_inherent(_: &Self::Call, _: &InherentData) -> Result<(), Self::Error> {
		Ok(())
	}
}
