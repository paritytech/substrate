// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Types to pause calls in the runtime.

/// Can pause specific transactions from being processed.
///
/// Note that paused transactions will not be queued for later execution. Instead they will be
/// dropped.
pub trait TransactionPause {
	/// How to unambiguously identify a call.
	///
	/// For example `(pallet_index, call_index)`.
	type CallIdentifier;

	/// Whether this call is paused.
	fn is_paused(call: Self::CallIdentifier) -> bool;

	/// Whether this call can be paused.
	///
	/// This holds for the current block, but may change in the future.
	fn can_pause(call: Self::CallIdentifier) -> bool;

	/// Pause this call immediately.
	///
	/// This takes effect in the same block and must succeed if `can_pause` returns `true`.
	fn pause(call: Self::CallIdentifier) -> Result<(), TransactionPauseError>;

	/// Unpause this call immediately.
	///
	/// This takes effect in the same block and must succeed if `is_paused` returns `true`. This
	/// invariant is important to not have un-resumable calls.
	fn unpause(call: Self::CallIdentifier) -> Result<(), TransactionPauseError>;
}

/// The error type for [`TransactionPause`].
pub enum TransactionPauseError {
	/// The call could not be found in the runtime.
	///
	/// This is a permanent error but could change after a runtime upgrade.
	NotFound,
	/// Call cannot be paused.
	///
	/// This may or may not resolve in a future block.
	Unpausable,
	/// Call is already paused.
	AlreadyPaused,
	/// Call is already unpaused.
	AlreadyUnpaused,
	/// Unknown error.
	Unknown,
}
