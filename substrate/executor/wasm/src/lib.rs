#![no_std]
#![feature(panic_implementation)]
#![cfg_attr(feature = "strict", deny(warnings))]

#![feature(alloc)]
extern crate alloc;
use alloc::vec::Vec;

#[macro_use]
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_sandbox as sandbox;

use runtime_io::{
	set_storage, storage, print, blake2_256,
	twox_128, twox_256, ed25519_verify, enumerated_trie_root
};

impl_stubs!(
	test_data_in NO_DECODE => |input| {
		print("set_storage");
		set_storage(b"input", input);

		print("storage");
		let foo = storage(b"foo").unwrap();

		print("set_storage");
		set_storage(b"baz", &foo);

		print("finished!");
		b"all ok!".to_vec()
	},
	test_empty_return NO_DECODE => |_| Vec::new(),
	test_panic NO_DECODE => |_| panic!("test panic"),
	test_conditional_panic NO_DECODE => |input: &[u8]| {
		if input.len() > 0 {
			panic!("test panic")
		}
		input.to_vec()
	},
	test_blake2_256 NO_DECODE => |input| blake2_256(input).to_vec(),
	test_twox_256 NO_DECODE => |input| twox_256(input).to_vec(),
	test_twox_128 NO_DECODE => |input| twox_128(input).to_vec(),
	test_ed25519_verify NO_DECODE => |input: &[u8]| {
		let mut pubkey = [0; 32];
		let mut sig = [0; 64];

		pubkey.copy_from_slice(&input[0..32]);
		sig.copy_from_slice(&input[32..96]);

		let msg = b"all ok!";
		[ed25519_verify(&sig, &msg[..], &pubkey) as u8].to_vec()
	},
	test_enumerated_trie_root NO_DECODE => |_| {
		enumerated_trie_root(&[&b"zero"[..], &b"one"[..], &b"two"[..]]).to_vec()
	},
	test_sandbox NO_DECODE => |code: &[u8]| {
		let ok = execute_sandboxed(code, &[]).is_ok();
		[ok as u8].to_vec()
	},
	test_sandbox_args NO_DECODE => |code: &[u8]| {
		let ok = execute_sandboxed(
			code,
			&[
				sandbox::TypedValue::I32(0x12345678),
				sandbox::TypedValue::I64(0x1234567887654321),
			]
		).is_ok();
		[ok as u8].to_vec()
	},
	test_sandbox_return_val NO_DECODE => |code: &[u8]| {
		let result = execute_sandboxed(
			code,
			&[
				sandbox::TypedValue::I32(0x1336),
			]
		);
		let ok = if let Ok(sandbox::ReturnValue::Value(sandbox::TypedValue::I32(0x1337))) = result { true } else { false };
		[ok as u8].to_vec()
	}
);

fn execute_sandboxed(code: &[u8], args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
	struct State {
		counter: u32,
	}

	fn env_assert(_e: &mut State, args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
		if args.len() != 1 {
			return Err(sandbox::HostError);
		}
		let condition = args[0].as_i32().ok_or_else(|| sandbox::HostError)?;
		if condition != 0 {
			Ok(sandbox::ReturnValue::Unit)
		} else {
			Err(sandbox::HostError)
		}
	}
	fn env_inc_counter(e: &mut State, args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
		if args.len() != 1 {
			return Err(sandbox::HostError);
		}
		let inc_by = args[0].as_i32().ok_or_else(|| sandbox::HostError)?;
		e.counter += inc_by as u32;
		Ok(sandbox::ReturnValue::Value(sandbox::TypedValue::I32(e.counter as i32)))
	}

	let mut state = State { counter: 0 };

	let mut env_builder = sandbox::EnvironmentDefinitionBuilder::new();
	env_builder.add_host_func("env", "assert", env_assert);
	env_builder.add_host_func("env", "inc_counter", env_inc_counter);

	let mut instance = sandbox::Instance::new(code, &env_builder, &mut state)?;
	let result = instance.invoke(b"call", args, &mut state);

	result.map_err(|_| sandbox::HostError)
}
