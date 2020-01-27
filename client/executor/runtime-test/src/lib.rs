#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "strict", deny(warnings))]

// Make the WASM binary available.
#[cfg(feature = "std")]
include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));

#[cfg(not(feature = "std"))]
use sp_std::{vec::Vec, vec};

#[cfg(not(feature = "std"))]
use sp_io::{
	storage, hashing::{blake2_128, blake2_256, sha2_256, twox_128, twox_256},
	crypto::{ed25519_verify, sr25519_verify},
};
#[cfg(not(feature = "std"))]
use sp_runtime::{print, traits::{BlakeTwo256, Hash}};
#[cfg(not(feature = "std"))]
use sp_core::{ed25519, sr25519};

extern "C" {
	#[allow(dead_code)]
	fn missing_external();

	#[allow(dead_code)]
	fn yet_another_missing_external();
}

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
		storage::clear_prefix(&input);
		b"all ok!".to_vec()
	}

	fn test_empty_return() {}

	fn test_exhaust_heap() -> Vec<u8> { Vec::with_capacity(16777216) }

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
		).as_ref().to_vec()
	}

	fn test_sandbox(code: Vec<u8>) -> bool {
		execute_sandboxed(&code, &[]).is_ok()
	}

	fn test_sandbox_args(code: Vec<u8>) -> bool {
		execute_sandboxed(
			&code,
			&[
				sp_sandbox::TypedValue::I32(0x12345678),
				sp_sandbox::TypedValue::I64(0x1234567887654321),
			],
		).is_ok()
	}

	fn test_sandbox_return_val(code: Vec<u8>) -> bool {
		let ok = match execute_sandboxed(
			&code,
			&[
				sp_sandbox::TypedValue::I32(0x1336),
			]
		) {
			Ok(sp_sandbox::ReturnValue::Value(sp_sandbox::TypedValue::I32(0x1337))) => true,
			_ => false,
		};

		ok
	}

	fn test_sandbox_instantiate(code: Vec<u8>) -> u8 {
		let env_builder = sp_sandbox::EnvironmentDefinitionBuilder::new();
		let code = match sp_sandbox::Instance::new(&code, &env_builder, &mut ()) {
			Ok(_) => 0,
			Err(sp_sandbox::Error::Module) => 1,
			Err(sp_sandbox::Error::Execution) => 2,
			Err(sp_sandbox::Error::OutOfBounds) => 3,
		};

		code
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

	// Just some test to make sure that `sp-allocator` compiles on `no_std`.
	fn test_sp_allocator_compiles() {
		sp_allocator::FreeingBumpHeapAllocator::new(0);
	}
 }

#[cfg(not(feature = "std"))]
fn execute_sandboxed(
	code: &[u8],
	args: &[sp_sandbox::TypedValue],
) -> Result<sp_sandbox::ReturnValue, sp_sandbox::HostError> {
	struct State {
		counter: u32,
	}

	fn env_assert(
		_e: &mut State,
		args: &[sp_sandbox::TypedValue],
	) -> Result<sp_sandbox::ReturnValue, sp_sandbox::HostError> {
		if args.len() != 1 {
			return Err(sp_sandbox::HostError);
		}
		let condition = args[0].as_i32().ok_or_else(|| sp_sandbox::HostError)?;
		if condition != 0 {
			Ok(sp_sandbox::ReturnValue::Unit)
		} else {
			Err(sp_sandbox::HostError)
		}
	}
	fn env_inc_counter(
		e: &mut State,
		args: &[sp_sandbox::TypedValue],
	) -> Result<sp_sandbox::ReturnValue, sp_sandbox::HostError> {
		if args.len() != 1 {
			return Err(sp_sandbox::HostError);
		}
		let inc_by = args[0].as_i32().ok_or_else(|| sp_sandbox::HostError)?;
		e.counter += inc_by as u32;
		Ok(sp_sandbox::ReturnValue::Value(sp_sandbox::TypedValue::I32(e.counter as i32)))
	}

	let mut state = State { counter: 0 };

	let env_builder = {
		let mut env_builder = sp_sandbox::EnvironmentDefinitionBuilder::new();
		env_builder.add_host_func("env", "assert", env_assert);
		env_builder.add_host_func("env", "inc_counter", env_inc_counter);
		let memory = match sp_sandbox::Memory::new(1, Some(16)) {
			Ok(m) => m,
			Err(_) => unreachable!("
				Memory::new() can return Err only if parameters are borked; \
				We passing params here explicitly and they're correct; \
				Memory::new() can't return a Error qed"
			),
		};
		env_builder.add_memory("env", "memory", memory.clone());
		env_builder
	};

	let mut instance = sp_sandbox::Instance::new(code, &env_builder, &mut state)?;
	let result = instance.invoke("call", args, &mut state);

	result.map_err(|_| sp_sandbox::HostError)
}
