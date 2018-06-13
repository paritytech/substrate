#![warn(missing_docs)]
#![cfg_attr(feature = "strict", deny(warnings))]
#![no_std]
#![crate_type = "rlib"]

//! Custom allocator crate for wasm

/// Wasm allocator
pub struct WasmAllocator;

#[cfg(feature = "nightly")]
#[global_allocator]
static ALLOCATOR: WasmAllocator = WasmAllocator;

#[cfg(feature = "nightly")]
mod __impl {
	extern crate pwasm_libc;

	use core::alloc::{GlobalAlloc, Layout};

	use super::WasmAllocator;

	unsafe impl GlobalAlloc for WasmAllocator {
		unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
			pwasm_libc::malloc(layout.size()) as *mut u8
		}

		unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
			pwasm_libc::free(ptr as *mut u8)
		}
	}
}
