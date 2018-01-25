#![warn(missing_docs)]
#![cfg_attr(feature = "strict", deny(warnings))]
#![no_std]

//! libc externs crate

extern "C" {
	fn ext_memcpy(dest: *mut u8, src: *const u8, n: usize) -> *mut u8;
	fn ext_memmove(dest: *mut u8, src: *const u8, n: usize) -> *mut u8;
	fn ext_memset(dest: *mut u8, c: i32, n: usize) -> *mut u8;
	fn ext_memcmp(s1: *const u8, s2: *const u8, n: usize) -> i32;
	fn ext_malloc(size: usize) -> *mut u8;
	fn ext_free(ptr: *mut u8);
}

// Declaring these function here prevents Emscripten from including it's own verisons
// into final binary.

/// memcpy extern
#[no_mangle]
pub unsafe extern "C" fn memcpy(dest: *mut u8, src: *const u8, n: usize) -> *mut u8 {
	ext_memcpy(dest, src, n)
}

/// memcpy extern
#[no_mangle]
pub unsafe extern "C" fn memcmp(s1: *const u8, s2: *const u8, n: usize) -> i32 {
	ext_memcmp(s1, s2, n)
}

/// memmove extern
#[no_mangle]
pub unsafe extern "C" fn memmove(dest: *mut u8, src: *const u8, n: usize) -> *mut u8 {
	ext_memmove(dest, src, n)
}

/// memset extern
#[no_mangle]
pub unsafe extern "C" fn memset(dest: *mut u8, c: i32, n: usize) -> *mut u8 {
	ext_memset(dest, c, n)
}

/// malloc extern
#[no_mangle]
pub unsafe extern "C" fn malloc(size: usize) -> *mut u8 {
	ext_malloc(size)
}

/// free extern
#[no_mangle]
pub unsafe extern "C" fn free(ptr: *mut u8) {
	ext_free(ptr);
}
