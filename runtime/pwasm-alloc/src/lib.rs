#![warn(missing_docs)]
#![cfg_attr(feature = "strict", deny(warnings))]
#![no_std]
#![crate_type = "rlib"]
#![feature(global_allocator)]
#![feature(alloc)]
#![feature(allocator_api)]

//! Custom allocator crate for wasm

extern crate alloc;
extern crate pwasm_libc;

use alloc::heap::{Alloc, Layout, AllocErr};

/// Wasm allocator
pub struct WasmAllocator;

unsafe impl<'a> Alloc for &'a WasmAllocator {
	unsafe fn alloc(&mut self, layout: Layout) -> Result<*mut u8, AllocErr> {
		Ok(pwasm_libc::malloc(layout.size()))
	}

	unsafe fn dealloc(&mut self, ptr: *mut u8, _layout: Layout) {
		pwasm_libc::free(ptr)
	}
}

#[global_allocator]
static ALLOCATOR: WasmAllocator = WasmAllocator;
