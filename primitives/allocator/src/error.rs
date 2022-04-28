// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

/// The error type used by the allocators.
#[derive(sp_std::fmt::Debug)]
pub enum Error {
	/// Someone tried to allocate more memory than the allowed maximum per allocation.
	RequestedAllocationTooLarge,
	/// Allocator run out of space.
	AllocatorOutOfSpace,
	/// The client passed a memory instance which is smaller than previously observed.
	MemoryShrinked,
	/// Some other error occurred.
	Other(&'static str),
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

impl sp_std::fmt::Display for Error {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		match self {
			Self::RequestedAllocationTooLarge => write!(f, "Requested allocation size is too large"),
			Self::AllocatorOutOfSpace => write!(f, "Allocator ran out of space"),
			Self::MemoryShrinked => write!(f, "Shrinking of the underlying memory is observed"),
			Self::Other(s) => write!(f, "Other: {}", s),
		}
	}
}
