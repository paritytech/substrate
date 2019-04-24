// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#[cfg(feature = "nightly")]
#[doc(hidden)]
pub extern crate alloc;

extern "C" {
	fn ext_malloc(size: usize) -> *mut u8;
	fn ext_free(ptr: *mut u8);
}

/// Wasm allocator
pub struct WasmAllocator;

#[global_allocator]
static ALLOCATOR: WasmAllocator = WasmAllocator;

mod __impl {
	use core::alloc::{GlobalAlloc, Layout};

	use super::WasmAllocator;

	unsafe impl GlobalAlloc for WasmAllocator {
		unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
			super::ext_malloc(layout.size()) as *mut u8
		}

		unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
			super::ext_free(ptr as *mut u8)
		}
	}
}

pub use alloc::boxed;
pub use alloc::rc;
pub use alloc::vec;
pub use core::borrow;
pub use core::cell;
pub use core::clone;
pub use core::cmp;
pub use core::hash;
pub use core::intrinsics;
pub use core::iter;
pub use core::marker;
pub use core::mem;
pub use core::num;
pub use core::ops;
pub use core::ptr;
pub use core::slice;
pub use core::result;
// We are trying to avoid certain things here, such as `core::string`
// (if you need `String` you most probably doing something wrong, since
// runtime doesn't require anything human readable).

pub mod collections {
	pub use alloc::collections::btree_map;
}
