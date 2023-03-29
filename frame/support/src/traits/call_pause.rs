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

//! Traits that can be used to pause calls.

pub trait SafeMode {
	type BlockNumber;

	/// Whether the safe mode is entered.
	fn is_entered() -> bool {
		Self::remaining().is_some()
	}

	/// How many more blocks the safe mode will stay entered.
	///
	/// If this returns `0` then the safe mode will exit in the next block.
	fn remaining() -> Option<Self::BlockNumber>;

	fn enter(duration: Self::BlockNumber) -> Result<(), SafeModeError>;

	fn extend(duration: Self::BlockNumber) -> Result<(), SafeModeError>;

	fn exit() -> Result<(), SafeModeError>;
}

pub enum SafeModeError {
	/// The safe mode is already entered.
	AlreadyEntered,
	/// The safe mode is already exited.
	AlreadyExited,
	Unknown,
}

pub trait TransactionPause {
	/// How to unambiguously identify a call.
	///
	/// For example `(pallet_index, call_index)`.
	type CallIdentifier;

	fn is_paused(call: Self::CallIdentifier) -> bool;

	fn can_pause(call: Self::CallIdentifier) -> bool;

	fn pause(call: Self::CallIdentifier) -> Result<(), TransactionPauseError>;

	fn unpause(call: Self::CallIdentifier) -> Result<(), TransactionPauseError>;
}

pub enum TransactionPauseError {
	/// The call could not be found in the runtime. This is a permanent error.
	NotFound,
	/// Call cannot be paused. This may or may not resolve in the future.
	Unpausable,
	/// Call is already paused.
	AlreadyPaused,
	/// Call is already unpaused.
	AlreadyUnpaused,
	Unknown,
}
