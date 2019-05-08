// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

#[cfg(feature = "nightly")]
#[doc(hidden)]
pub extern crate alloc;

extern "C" {
	fn ext_malloc(size: usize) -> *mut u8;
	fn ext_free(ptr: *mut u8);
}

/// Wasm allocator
pub struct WasmAllocator;

#[cfg(not(feature = "no_global_allocator"))]
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
pub use core::default;
pub use core::result;
pub use core::convert;
// We are trying to avoid certain things here, such as `core::string`
// (if you need `String` you most probably doing something wrong, since
// runtime doesn't require anything human readable).

pub mod collections {
	pub use alloc::collections::btree_map;
	pub use alloc::collections::btree_set;
}
