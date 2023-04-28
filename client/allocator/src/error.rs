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

/// Error indicating that the state of the allocator is corrupt.
#[derive(thiserror::Error, Debug, PartialEq)]
pub enum PoisonedError {
	/// The client passed a memory instance which is smaller than previously observed.
	#[error("Shrinking of the underlying memory is observed")]
	MemoryShrinked,
	/// More pages than permitted were allocated.
	#[error("The pages limit was already exceeded")]
	PagesLimitExceeded,
	/// Some other error occurred.
	#[error("Other: {0}")]
	Other(&'static str),
}

#[derive(thiserror::Error, Debug, PartialEq)]
pub enum RecoverableError {
	/// Someone tried to allocate more memory than the allowed maximum per allocation.
	#[error("Requested allocation size is too large")]
	RequestedAllocationTooLarge,
	/// Allocator run out of space.
	#[error("Allocator ran out of space")]
	AllocatorOutOfSpace,
	/// Some other error occurred.
	#[error("Other: {0}")]
	Other(&'static str),
}

/// The error type used by the allocators.
#[derive(thiserror::Error, Debug, PartialEq)]
pub(crate) enum Error {
	#[error("Poisoned error: {0}")]
	Poisoned(PoisonedError),
	#[error("Recoverable error: {0}")]
	Recoverable(RecoverableError),
}

impl Error {
	/// Check if the error is poisoned.
	pub fn recover_or_poison<T>(self, default: T, poisoned: &mut bool) -> Result<T, PoisonedError> {
		if let Error::Poisoned(e) = self {
			*poisoned = true;
			return Err(e)
		}

		Ok(default)
	}
}

impl From<PoisonedError> for Error {
	fn from(value: PoisonedError) -> Self {
		Error::Poisoned(value)
	}
}

impl From<RecoverableError> for Error {
	fn from(value: RecoverableError) -> Self {
		Error::Recoverable(value)
	}
}
