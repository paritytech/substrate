#![cfg_attr(not(feature = "std"), no_std)]

// Make the WASM binary available.
#[cfg(feature = "std")]
include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));

/// Wasm binary unwrapped. If built with `SKIP_WASM_BUILD`, the function panics.
#[cfg(feature = "std")]
pub fn wasm_binary_unwrap() -> &'static [u8] {
	WASM_BINARY.expect(
		"Development wasm binary is not available. Testing is only supported with the flag \
		 disabled.",
	)
}

#[cfg(not(feature = "std"))]
use sp_std::{vec, vec::Vec};

#[cfg(not(feature = "std"))]
use sp_core::{ed25519, sr25519};
#[cfg(not(feature = "std"))]
use sp_io::{
	crypto::{ed25519_verify, sr25519_verify},
	hashing::{blake2_128, blake2_256, sha2_256, twox_128, twox_256},
	storage, wasm_tracing, RiscvExecOutcome, RiscvState,
};
#[cfg(not(feature = "std"))]
use sp_runtime::{
	print,
	traits::{BlakeTwo256, Hash},
};

extern "C" {
	#[allow(dead_code)]
	fn missing_external();

	#[allow(dead_code)]
	fn yet_another_missing_external();
}

#[cfg(not(feature = "std"))]
/// The size of a WASM page in bytes.
const WASM_PAGE_SIZE: usize = 65536;

#[cfg(not(feature = "std"))]
/// Mutable static variables should be always observed to have
/// the initialized value at the start of a runtime call.
static mut MUTABLE_STATIC: u64 = 32;

#[cfg(not(feature = "std"))]
/// This is similar to `MUTABLE_STATIC`. The tests need `MUTABLE_STATIC` for testing that
/// non-null initialization data is properly restored during instance reusing.
///
/// `MUTABLE_STATIC_BSS` on the other hand focuses on the zeroed data. This is important since there
/// may be differences in handling zeroed and non-zeroed data.
static mut MUTABLE_STATIC_BSS: u64 = 0;

sp_core::wasm_export_functions! {
	fn test_calling_missing_external() {
		unsafe { missing_external() }
	}

	fn test_calling_yet_another_missing_external() {
		unsafe { yet_another_missing_external() }
	}

	fn test_data_in(input: Vec<u8>) -> Vec<u8> {
		print("set_storage");
		storage::set(b"input", &input);

		print("storage");
		let foo = storage::get(b"foo").unwrap();

		print("set_storage");
		storage::set(b"baz", &foo);

		print("finished!");
		b"all ok!".to_vec()
	}

	fn test_clear_prefix(input: Vec<u8>) -> Vec<u8> {
		storage::clear_prefix(&input, None);
		b"all ok!".to_vec()
	}

	fn test_empty_return() {}

	fn test_dirty_plenty_memory(heap_base: u32, heap_pages: u32) {
		// This piece of code will dirty multiple pages of memory. The number of pages is given by
		// the `heap_pages`. It's unit is a wasm page (64KiB). The first page to be cleared
		// is a wasm page that that follows the one that holds the `heap_base` address.
		//
		// This function dirties the **host** pages. I.e. we dirty 4KiB at a time and it will take
		// 16 writes to process a single wasm page.

		let heap_ptr = heap_base as usize;

		// Find the next wasm page boundary.
		let heap_ptr = round_up_to(heap_ptr, WASM_PAGE_SIZE);

		// Make it an actual pointer
		let heap_ptr = heap_ptr as *mut u8;

		// Traverse the host pages and make each one dirty
		let host_pages = heap_pages as usize * 16;
		for i in 0..host_pages {
			unsafe {
				// technically this is an UB, but there is no way Rust can find this out.
				heap_ptr.add(i * 4096).write(0);
			}
		}

		fn round_up_to(n: usize, divisor: usize) -> usize {
			(n + divisor - 1) / divisor
		}
	}

	fn test_allocate_vec(size: u32) -> Vec<u8> {
		Vec::with_capacity(size as usize)
	}

	fn test_fp_f32add(a: [u8; 4], b: [u8; 4]) -> [u8; 4] {
		let a = f32::from_le_bytes(a);
		let b = f32::from_le_bytes(b);
		f32::to_le_bytes(a + b)
	}

	fn test_panic() { panic!("test panic") }

	fn test_conditional_panic(input: Vec<u8>) -> Vec<u8> {
		if input.len() > 0 {
			panic!("test panic")
		}

		input
	}

	fn test_blake2_256(input: Vec<u8>) -> Vec<u8> {
		blake2_256(&input).to_vec()
	}

	fn test_blake2_128(input: Vec<u8>) -> Vec<u8> {
		blake2_128(&input).to_vec()
	}

	fn test_sha2_256(input: Vec<u8>) -> Vec<u8> {
		sha2_256(&input).to_vec()
	}

	fn test_twox_256(input: Vec<u8>) -> Vec<u8> {
		twox_256(&input).to_vec()
	}

	fn test_twox_128(input: Vec<u8>) -> Vec<u8> {
		twox_128(&input).to_vec()
	}

	fn test_ed25519_verify(input: Vec<u8>) -> bool {
		let mut pubkey = [0; 32];
		let mut sig = [0; 64];

		pubkey.copy_from_slice(&input[0..32]);
		sig.copy_from_slice(&input[32..96]);

		let msg = b"all ok!";
		ed25519_verify(&ed25519::Signature(sig), &msg[..], &ed25519::Public(pubkey))
	}

	fn test_sr25519_verify(input: Vec<u8>) -> bool {
		let mut pubkey = [0; 32];
		let mut sig = [0; 64];

		pubkey.copy_from_slice(&input[0..32]);
		sig.copy_from_slice(&input[32..96]);

		let msg = b"all ok!";
		sr25519_verify(&sr25519::Signature(sig), &msg[..], &sr25519::Public(pubkey))
	}

	fn test_ordered_trie_root() -> Vec<u8> {
		BlakeTwo256::ordered_trie_root(
			vec![
				b"zero"[..].into(),
				b"one"[..].into(),
				b"two"[..].into(),
			],
			sp_core::storage::StateVersion::V1,
		).as_ref().to_vec()
	}

	fn test_offchain_index_set() {
		sp_io::offchain_index::set(b"k", b"v");
	}

	fn test_offchain_local_storage() -> bool {
		let kind = sp_core::offchain::StorageKind::PERSISTENT;
		assert_eq!(sp_io::offchain::local_storage_get(kind, b"test"), None);
		sp_io::offchain::local_storage_set(kind, b"test", b"asd");
		assert_eq!(sp_io::offchain::local_storage_get(kind, b"test"), Some(b"asd".to_vec()));

		let res = sp_io::offchain::local_storage_compare_and_set(
			kind,
			b"test",
			Some(b"asd".to_vec()),
			b"",
		);
		assert_eq!(sp_io::offchain::local_storage_get(kind, b"test"), Some(b"".to_vec()));
		res
	}

	fn test_offchain_local_storage_with_none() {
		let kind = sp_core::offchain::StorageKind::PERSISTENT;
		assert_eq!(sp_io::offchain::local_storage_get(kind, b"test"), None);

		let res = sp_io::offchain::local_storage_compare_and_set(kind, b"test", None, b"value");
		assert_eq!(res, true);
		assert_eq!(sp_io::offchain::local_storage_get(kind, b"test"), Some(b"value".to_vec()));
	}

	fn test_offchain_http() -> bool {
		use sp_core::offchain::HttpRequestStatus;
		let run = || -> Option<()> {
			let id = sp_io::offchain::http_request_start(
				"POST",
				"http://localhost:12345",
				&[],
			).ok()?;
			sp_io::offchain::http_request_add_header(id, "X-Auth", "test").ok()?;
			sp_io::offchain::http_request_write_body(id, &[1, 2, 3, 4], None).ok()?;
			sp_io::offchain::http_request_write_body(id, &[], None).ok()?;
			let status = sp_io::offchain::http_response_wait(&[id], None);
			assert!(status == vec![HttpRequestStatus::Finished(200)], "Expected Finished(200) status.");
			let headers = sp_io::offchain::http_response_headers(id);
			assert_eq!(headers, vec![(b"X-Auth".to_vec(), b"hello".to_vec())]);
			let mut buffer = vec![0; 64];
			let read = sp_io::offchain::http_response_read_body(id, &mut buffer, None).ok()?;
			assert_eq!(read, 3);
			assert_eq!(&buffer[0..read as usize], &[1, 2, 3]);
			let read = sp_io::offchain::http_response_read_body(id, &mut buffer, None).ok()?;
			assert_eq!(read, 0);

			Some(())
		};

		run().is_some()
	}

	fn test_enter_span() -> u64 {
		wasm_tracing::enter_span(Default::default())
	}

	fn test_exit_span(span_id: u64) {
		wasm_tracing::exit(span_id)
	}

	fn test_nested_spans() {
		sp_io::init_tracing();
		let span_id = wasm_tracing::enter_span(Default::default());
		{
			sp_io::init_tracing();
			let span_id = wasm_tracing::enter_span(Default::default());
			wasm_tracing::exit(span_id);
		}
		wasm_tracing::exit(span_id);
	}

	fn returns_mutable_static() -> u64 {
		unsafe {
			MUTABLE_STATIC += 1;
			MUTABLE_STATIC
		}
	}

	fn returns_mutable_static_bss() -> u64 {
		unsafe {
			MUTABLE_STATIC_BSS += 1;
			MUTABLE_STATIC_BSS
		}
	}

	fn allocates_huge_stack_array(trap: bool) -> Vec<u8> {
		// Allocate a stack frame that is approx. 75% of the stack (assuming it is 1MB).
		// This will just decrease (stacks in wasm32-u-u grow downwards) the stack
		// pointer. This won't trap on the current compilers.
		let mut data = [0u8; 1024 * 768];

		// Then make sure we actually write something to it.
		//
		// If:
		// 1. the stack area is placed at the beginning of the linear memory space, and
		// 2. the stack pointer points to out-of-bounds area, and
		// 3. a write is performed around the current stack pointer.
		//
		// then a trap should happen.
		//
		for (i, v) in data.iter_mut().enumerate() {
			*v = i as u8; // deliberate truncation
		}

		if trap {
			// There is a small chance of this to be pulled up in theory. In practice
			// the probability of that is rather low.
			panic!()
		}

		data.to_vec()
	}

	// Check that the heap at `heap_base + offset` don't contains the test message.
	// After the check succeeds the test message is written into the heap.
	//
	// It is expected that the given pointer is not allocated.
	fn check_and_set_in_heap(heap_base: u32, offset: u32) {
		let test_message = b"Hello invalid heap memory";
		let ptr = (heap_base + offset) as *mut u8;

		let message_slice = unsafe { sp_std::slice::from_raw_parts_mut(ptr, test_message.len()) };

		assert_ne!(test_message, message_slice);
		message_slice.copy_from_slice(test_message);
	}

	fn test_return_i8() -> i8 {
		-66
	}

	fn test_take_i8(value: i8) {
		assert_eq!(value, -66);
	}

	fn allocate_two_gigabyte() -> u32 {
		let mut data = Vec::new();
		for _ in 0..205 {
			data.push(Vec::<u8>::with_capacity(10 * 1024 * 1024));
		}

		data.iter().map(|d| d.capacity() as u32).sum()
	}

	fn test_abort_on_panic() {
		sp_io::panic_handler::abort_on_panic("test_abort_on_panic called");
	}

	fn test_unreachable_intrinsic() {
		core::arch::wasm32::unreachable()
	}

	fn test_return_value() -> u64 {
		// Mainly a test that the macro is working when we have a return statement here.
		return 1234;
	}

	fn test_riscv() {
		let program = include_bytes!("../riscv-test-guest.elf");
		execute_riscv(program.as_ref());
	}
}

// Tests that check output validity. We explicitly return the ptr and len, so we avoid using the
// `wasm_export_functions` macro.
mod output_validity {
	#[cfg(not(feature = "std"))]
	use super::WASM_PAGE_SIZE;

	#[cfg(not(feature = "std"))]
	use sp_runtime_interface::pack_ptr_and_len;

	// Returns a huge len. It should result in an error, and not an allocation.
	#[no_mangle]
	#[cfg(not(feature = "std"))]
	pub extern "C" fn test_return_huge_len(_params: *const u8, _len: usize) -> u64 {
		pack_ptr_and_len(0, u32::MAX)
	}

	// Returns an offset right before the edge of the wasm memory boundary. It should succeed.
	#[no_mangle]
	#[cfg(not(feature = "std"))]
	pub extern "C" fn test_return_max_memory_offset(_params: *const u8, _len: usize) -> u64 {
		let output_ptr = (core::arch::wasm32::memory_size(0) * WASM_PAGE_SIZE) as u32 - 1;
		let ptr = output_ptr as *mut u8;
		unsafe {
			ptr.write(u8::MAX);
		}
		pack_ptr_and_len(output_ptr, 1)
	}

	// Returns an offset right after the edge of the wasm memory boundary. It should fail.
	#[no_mangle]
	#[cfg(not(feature = "std"))]
	pub extern "C" fn test_return_max_memory_offset_plus_one(
		_params: *const u8,
		_len: usize,
	) -> u64 {
		pack_ptr_and_len((core::arch::wasm32::memory_size(0) * WASM_PAGE_SIZE) as u32, 1)
	}

	// Returns an output that overflows the u32 range. It should result in an error.
	#[no_mangle]
	#[cfg(not(feature = "std"))]
	pub extern "C" fn test_return_overflow(_params: *const u8, _len: usize) -> u64 {
		pack_ptr_and_len(u32::MAX, 1)
	}
}

#[cfg(not(feature = "std"))]
fn execute_riscv(program: &[u8]) {
	struct State {
		counter: u64,
	}

	unsafe extern "C" fn syscall_handler(
		state: &mut RiscvState<State>,
		a0: u32,
		a1: u32,
		_a2: u32,
		_a3: u32,
		_a4: u32,
		_a5: u32,
	) -> u64 {
		match a0 {
			// read counter
			1 => {
				let buf = state.user.counter.to_le_bytes();
				sp_io::riscv::write_memory(a1, buf.as_ptr() as u32, buf.len() as u32);
			},
			// increment counter
			2 => {
				let mut buf = [0u8; 8];
				sp_io::riscv::read_memory(a1, buf.as_mut_ptr() as u32, buf.len() as u32);
				state.user.counter += u64::from_le_bytes(buf);
			},
			// exit (`ret` from entry point is not possible)
			3 => {
				state.exit = true;
			},
			_ => panic!("unknown syscall: {}", a0),
		}
		u64::from(a0) << 32
	}

	// start counter at 0 (passed in a0)
	let mut state = RiscvState { fuel_left: 0, exit: false, user: State { counter: 0 } };
	let ret =
		sp_io::riscv::execute(program, 0, syscall_handler as u32, &mut state as *mut _ as u32);
	assert_eq!(ret, RiscvExecOutcome::Ok);
	assert_eq!(state.user.counter, 8);

	// start counter at 21 (passed in a0)
	let mut state = RiscvState { fuel_left: 0, exit: false, user: State { counter: 0 } };
	let ret =
		sp_io::riscv::execute(program, 21, syscall_handler as u32, &mut state as *mut _ as u32);
	assert_eq!(ret, RiscvExecOutcome::Ok);
	assert_eq!(state.user.counter, 29);

	// pass 42 which makes the contract panic without doing any work
	let mut state = RiscvState { fuel_left: 0, exit: false, user: State { counter: 0 } };
	let ret =
		sp_io::riscv::execute(program, 42, syscall_handler as u32, &mut state as *mut _ as u32);
	assert_eq!(ret, RiscvExecOutcome::Trap);
	assert_eq!(state.user.counter, 0);
}
