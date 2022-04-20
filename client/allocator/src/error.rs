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
#[derive(thiserror::Error, Debug)]
pub enum Error {
	/// Someone tried to allocate more memory than the allowed maximum per allocation.
	#[error("Requested allocation size is too large")]
	RequestedAllocationTooLarge,
	/// Allocator run out of space.
	#[error("Allocator ran out of space")]
	AllocatorOutOfSpace,
	/// The client passed a memory instance which is smaller than previously observed.
	#[error("Shrinking of the underlying memory is observed")]
	MemoryShrinked,
	/// Some other error occurred.
	#[error("Other: {0}")]
	Other(&'static str),
}
