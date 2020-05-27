// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
#[derive(sp_core::RuntimeDebug)]
#[cfg_attr(feature = "std", derive(derive_more::Display))]
pub enum Error {
	/// Someone tried to allocate more memory than the allowed maximum per allocation.
	#[cfg_attr(feature = "std", display(fmt="Requested allocation size is too large"))]
	RequestedAllocationTooLarge,
	/// Allocator run out of space.
	#[cfg_attr(feature = "std", display(fmt="Allocator ran out of space"))]
	AllocatorOutOfSpace,
	/// Some other error occurred.
	Other(&'static str)
}

#[cfg(feature = "std")]
impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			_ => None,
		}
	}
}
