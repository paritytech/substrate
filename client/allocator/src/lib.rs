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

//! Collection of allocator implementations.
//!
//! This crate provides the following allocator implementations:
//! - A freeing-bump allocator: [`FreeingBumpHeapAllocator`](freeing_bump::FreeingBumpHeapAllocator)

#![warn(missing_docs)]

mod error;
mod freeing_bump;

pub use error::Error;
pub use freeing_bump::{AllocationStats, FreeingBumpHeapAllocator};

/// The size of one wasm page in bytes.
///
/// The wasm memory is divided into pages, meaning the minimum size of a memory is one page.
const PAGE_SIZE: u32 = 65536;

/// The maximum number of wasm pages that can be allocated.
///
/// 4GiB / [`PAGE_SIZE`].
const MAX_WASM_PAGES: u32 = (4u64 * 1024 * 1024 * 1024 / PAGE_SIZE as u64) as u32;

/// Grants access to the memory for the allocator.
///
/// Memory of wasm is allocated in pages. A page has a constant size of 64KiB. The maximum allowed
/// memory size as defined in the wasm specification is 4GiB (65536 pages).
pub trait Memory {
	/// Run the given closure `run` and grant it write access to the raw memory.
	fn with_access_mut<R>(&mut self, run: impl FnOnce(&mut [u8]) -> R) -> R;
	/// Run the given closure `run` and grant it read access to the raw memory.
	fn with_access<R>(&self, run: impl FnOnce(&[u8]) -> R) -> R;
	/// Grow the memory by `additional` pages.
	fn grow(&mut self, additional: u32) -> Result<(), ()>;
	/// Returns the current number of pages this memory has allocated.
	fn pages(&self) -> u32;
	/// Returns the maximum number of pages this memory is allowed to allocate.
	///
	/// The returned number needs to be smaller or equal to `65536`. The returned number needs to be
	/// bigger or equal to [`Self::pages`].
	///
	/// If `None` is returned, there is no maximum (besides the maximum defined in the wasm spec).
	fn max_pages(&self) -> Option<u32>;
}
