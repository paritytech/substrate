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

//! Types to put the runtime into safe mode.

/// Can put the runtime into a safe mode.
///
/// When the runtime entered safe mode, transaction processing for most general transactions is
/// paused.
pub trait SafeMode {
	/// Block number type.
	type BlockNumber;

	/// Whether safe mode is entered.
	fn is_entered() -> bool {
		Self::remaining().is_some()
	}

	/// How many more blocks safe mode will stay entered.
	///
	/// If this returns `0`, then safe mode will exit in the next block.
	fn remaining() -> Option<Self::BlockNumber>;

	/// Enter safe mode for `duration` blocks.
	///
	/// Should error when already entered with `AlreadyEntered`.
	fn enter(duration: Self::BlockNumber) -> Result<(), SafeModeError>;

	/// Extend safe mode for `duration` blocks.
	///
	/// Should error when not entered with `AlreadyExited`.
	fn extend(duration: Self::BlockNumber) -> Result<(), SafeModeError>;

	/// Exit safe mode immediately.
	///
	/// This takes effect already in the same block.
	fn exit() -> Result<(), SafeModeError>;
}

/// The error type for [`SafeMode`].
pub enum SafeModeError {
	/// Safe mode is already entered.
	AlreadyEntered,
	/// Safe mode is already exited.
	AlreadyExited,
	/// Unknown error.
	Unknown,
}

/// A trait to notify when the runtime enters or exits safe mode.
pub trait SafeModeNotify {
	/// Called when the runtime enters safe mode.
	fn entered();

	/// Called when the runtime exits safe mode.
	fn exited();
}

impl SafeModeNotify for () {
	fn entered() {}
	fn exited() {}
}
