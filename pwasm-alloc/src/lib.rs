#![warn(missing_docs)]
#![cfg_attr(feature = "strict", deny(warnings))]
#![no_std]
#![crate_type = "rlib"]
#![cfg_attr(feature = "nightly", feature(global_allocator))]
#![cfg_attr(feature = "nightly", feature(alloc))]
#![cfg_attr(feature = "nightly", feature(allocator_api))]

//! Custom allocator crate for wasm

/// Wasm allocator
pub struct WasmAllocator;

#[cfg(feature = "nightly")]
#[global_allocator]
static ALLOCATOR: WasmAllocator = WasmAllocator;

#[cfg(feature = "nightly")]
mod __impl {
	extern crate alloc;
	extern crate pwasm_libc;

	use self::alloc::heap::{Alloc, Layout, AllocErr};

	use super::WasmAllocator;

	unsafe impl<'a> Alloc for &'a WasmAllocator {
		unsafe fn alloc(&mut self, layout: Layout) -> Result<*mut u8, AllocErr> {
			Ok(pwasm_libc::malloc(layout.size()))
		}

		unsafe fn dealloc(&mut self, ptr: *mut u8, _layout: Layout) {
			pwasm_libc::free(ptr)
		}
	}
}
