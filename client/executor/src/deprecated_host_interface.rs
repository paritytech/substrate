// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Definition and implementation of the old and deprecated Substrate runtime interface for the host.

use codec::Encode;
use std::{convert::TryFrom, str};
use sp_core::{
	blake2_128, blake2_256, twox_64, twox_128, twox_256, ed25519, sr25519, keccak_256, Blake2Hasher, Pair,
	crypto::KeyTypeId, offchain,
};
use sp_trie::{TrieConfiguration, trie_types::Layout};
use sp_wasm_interface::{
	Pointer, WordSize, WritePrimitive, ReadPrimitive, FunctionContext, Result as WResult,
};

#[cfg(feature="wasm-extern-trace")]
macro_rules! debug_trace {
	( $( $x:tt )* ) => ( trace!( $( $x )* ) )
}

#[cfg(not(feature="wasm-extern-trace"))]
macro_rules! debug_trace {
	( $( $x:tt )* ) => ()
}

/// The old and deprecated Substrate externals. These are still required for backwards compatibility
/// reasons.
pub struct SubstrateExternals;

enum RecoverResult {
	Invalid(u32),
	Valid(secp256k1::PublicKey),
}

fn secp256k1_recover(
	context: &mut dyn FunctionContext,
	msg_data: Pointer<u8>,
	sig_data: Pointer<u8>,
) -> WResult<RecoverResult> {
	let mut sig = [0u8; 65];
	context.read_memory_into(sig_data, &mut sig[..])
		.map_err(|_| "Invalid attempt to get signature in ext_secp256k1_ecdsa_recover")?;
	let rs = match secp256k1::Signature::parse_slice(&sig[0..64]) {
		Ok(rs) => rs,
		_ => return Ok(RecoverResult::Invalid(1)),
	};

	let recovery_id = if sig[64] > 26 { sig[64] - 27 } else { sig[64] } as u8;
	let v = match secp256k1::RecoveryId::parse(recovery_id) {
		Ok(v) => v,
		_ => return Ok(RecoverResult::Invalid(2)),
	};

	let mut msg = [0u8; 32];
	context.read_memory_into(msg_data, &mut msg[..])
		.map_err(|_| "Invalid attempt to get message in ext_secp256k1_ecdsa_recover")?;

	Ok(match secp256k1::recover(&secp256k1::Message::parse(&msg), &rs, &v) {
		Ok(pubkey) => RecoverResult::Valid(pubkey),
		Err(_) => RecoverResult::Invalid(3),
	})
}

impl_wasm_host_interface! {
	impl SubstrateExternals where context {
		ext_malloc(size: WordSize) -> Pointer<u8> {
			let r = context.allocate_memory(size)?;
			debug_trace!(target: "sp-io", "malloc {} bytes at {:?}", size, r);
			Ok(r)
		}

		ext_free(addr: Pointer<u8>) {
			context.deallocate_memory(addr)?;
			debug_trace!(target: "sp-io", "free {:?}", addr);
			Ok(())
		}

		ext_sandbox_instantiate(
			dispatch_thunk_idx: u32,
			wasm_ptr: Pointer<u8>,
			wasm_len: WordSize,
			imports_ptr: Pointer<u8>,
			imports_len: WordSize,
			state: u32,
		) -> u32 {
			let wasm = context.read_memory(wasm_ptr, wasm_len)
				.map_err(|_| "OOB while ext_sandbox_instantiate: wasm")?;
			let raw_env_def = context.read_memory(imports_ptr, imports_len)
				.map_err(|_| "OOB while ext_sandbox_instantiate: imports")?;

			context.sandbox().instance_new(dispatch_thunk_idx, &wasm, &raw_env_def, state)
		}

		ext_sandbox_instance_teardown(instance_idx: u32) {
			context.sandbox().instance_teardown(instance_idx)
		}

		ext_sandbox_invoke(
			instance_idx: u32,
			export_ptr: Pointer<u8>,
			export_len: WordSize,
			args_ptr: Pointer<u8>,
			args_len: WordSize,
			return_val_ptr: Pointer<u8>,
			return_val_len: WordSize,
			state: u32,
		) -> u32 {
			let export = context.read_memory(export_ptr, export_len)
				.map_err(|_| "OOB while ext_sandbox_invoke: export")
				.and_then(|b|
					String::from_utf8(b)
						.map_err(|_| "Export name should be a valid utf-8 sequence")
				)?;

			// Deserialize arguments and convert them into wasmi types.
			let serialized_args = context.read_memory(args_ptr, args_len)
				.map_err(|_| "OOB while ext_sandbox_invoke: args")?;

			context.sandbox().invoke(
				instance_idx,
				&export,
				&serialized_args,
				return_val_ptr,
				return_val_len,
				state,
			)
		}

		ext_sandbox_memory_new(initial: WordSize, maximum: WordSize) -> u32 {
			context.sandbox().memory_new(initial, maximum)
		}

		ext_sandbox_memory_get(
			memory_idx: u32,
			offset: WordSize,
			buf_ptr: Pointer<u8>,
			buf_len: WordSize,
		) -> u32 {
			context.sandbox().memory_get(memory_idx, offset, buf_ptr, buf_len)
		}

		ext_sandbox_memory_set(
			memory_idx: u32,
			offset: WordSize,
			val_ptr: Pointer<u8>,
			val_len: WordSize,
		) -> u32 {
			context.sandbox().memory_set(memory_idx, offset, val_ptr, val_len)
		}

		ext_sandbox_memory_teardown(memory_idx: u32) {
			context.sandbox().memory_teardown(memory_idx)
		}

		ext_print_utf8(utf8_data: Pointer<u8>, utf8_len: WordSize) {
			if let Ok(utf8) = context.read_memory(utf8_data, utf8_len) {
				sp_io::misc::print_utf8(&utf8);
			}
			Ok(())
		}

		ext_print_hex(data: Pointer<u8>, len: WordSize) {
			if let Ok(hex) = context.read_memory(data, len) {
				sp_io::misc::print_hex(&hex);
			}
			Ok(())
		}

		ext_print_num(number: u64) {
			sp_io::misc::print_num(number);
			Ok(())
		}

		ext_log(
			level: u32,
			target_data: Pointer<u8>,
			target_len: WordSize,
			message_data: Pointer<u8>,
			message_len: WordSize,
		) {
			let target = context.read_memory(target_data, target_len)
				.map_err(|_| "Invalid attempt to determine target in ext_log")?;
			let message = context.read_memory(message_data, message_len)
				.map_err(|_| "Invalid attempt to determine message in ext_log")?;

			let target_str = std::str::from_utf8(&target)
				.map_err(|_| "Target invalid utf8 in ext_log")?;

			sp_io::logging::log(level.into(), &target_str, &message);
			Ok(())
		}

		ext_set_storage(
			key_data: Pointer<u8>,
			key_len: WordSize,
			value_data: Pointer<u8>,
			value_len: WordSize,
		) {
			let key = context.read_memory(key_data, key_len)
				.map_err(|_| "Invalid attempt to determine key in ext_set_storage")?;
			let value = context.read_memory(value_data, value_len)
				.map_err(|_| "Invalid attempt to determine value in ext_set_storage")?;
			Ok(sp_io::storage::set(&key, &value))
		}

		ext_clear_storage(key_data: Pointer<u8>, key_len: WordSize) {
			let key = context.read_memory(key_data, key_len)
				.map_err(|_| "Invalid attempt to determine key in ext_clear_storage")?;
			Ok(sp_io::storage::clear(&key))
		}

		ext_exists_storage(key_data: Pointer<u8>, key_len: WordSize) -> u32 {
			let key = context.read_memory(key_data, key_len)
				.map_err(|_| "Invalid attempt to determine key in ext_exists_storage")?;
			Ok(if sp_io::storage::exists(&key) { 1 } else { 0 })
		}

		ext_clear_prefix(prefix_data: Pointer<u8>, prefix_len: WordSize) {
			let prefix = context.read_memory(prefix_data, prefix_len)
				.map_err(|_| "Invalid attempt to determine prefix in ext_clear_prefix")?;
			Ok(sp_io::storage::clear_prefix(&prefix))
		}

		ext_get_allocated_storage(
			key_data: Pointer<u8>,
			key_len: WordSize,
			written_out: Pointer<u32>,
		) -> Pointer<u8> {
			let key = context.read_memory(key_data, key_len)
				.map_err(|_| "Invalid attempt to determine key in ext_get_allocated_storage")?;

			if let Some(value) = sp_io::storage::get(&key) {
				let offset = context.allocate_memory(value.len() as u32)?;
				context.write_memory(offset, &value)
					.map_err(|_| "Invalid attempt to set memory in ext_get_allocated_storage")?;
				context.write_primitive(written_out, value.len() as u32)
					.map_err(|_| "Invalid attempt to write written_out in ext_get_allocated_storage")?;
				Ok(offset)
			} else {
				context.write_primitive(written_out, u32::max_value())
					.map_err(|_| "Invalid attempt to write failed written_out in ext_get_allocated_storage")?;
				Ok(Pointer::null())
			}
		}

		ext_get_storage_into(
			key_data: Pointer<u8>,
			key_len: WordSize,
			value_data: Pointer<u8>,
			value_len: WordSize,
			value_offset: WordSize,
		) -> WordSize {
			let key = context.read_memory(key_data, key_len)
				.map_err(|_| "Invalid attempt to get key in ext_get_storage_into")?;

			if let Some(value) = sp_io::storage::get(&key) {
				let data = &value[value.len().min(value_offset as usize)..];
				let written = std::cmp::min(value_len as usize, data.len());
				context.write_memory(value_data, &data[..written])
					.map_err(|_| "Invalid attempt to set value in ext_get_storage_into")?;
				Ok(value.len() as u32)
			} else {
				Ok(u32::max_value())
			}
		}

		ext_storage_root(result: Pointer<u8>) {
			context.write_memory(result, sp_io::storage::root().as_ref())
				.map_err(|_| "Invalid attempt to set memory in ext_storage_root".into())
		}

		ext_storage_changes_root(
			parent_hash_data: Pointer<u8>,
			_len: WordSize,
			result: Pointer<u8>,
		) -> u32 {
			let mut parent_hash = [0u8; 32];
			context.read_memory_into(parent_hash_data, &mut parent_hash[..])
				.map_err(|_| "Invalid attempt to get parent_hash in ext_storage_changes_root")?;

			if let Some(r) = sp_io::storage::changes_root(&parent_hash) {
				context.write_memory(result, &r[..])
					.map_err(|_| "Invalid attempt to set memory in ext_storage_changes_root")?;
				Ok(1)
			} else {
				Ok(0)
			}
		}

		ext_blake2_256_enumerated_trie_root(
			values_data: Pointer<u8>,
			lens_data: Pointer<u32>,
			lens_len: WordSize,
			result: Pointer<u8>,
		) {
			let values = (0..lens_len)
				.map(|i| context.read_primitive(lens_data.offset(i).ok_or("Pointer overflow")?))
				.collect::<std::result::Result<Vec<u32>, _>>()?
				.into_iter()
				.scan(0u32, |acc, v| { let o = *acc; *acc += v; Some((o, v)) })
				.map(|(offset, len)|
					context.read_memory(values_data.offset(offset).ok_or("Pointer overflow")?, len)
						.map_err(|_|
							"Invalid attempt to get memory in ext_blake2_256_enumerated_trie_root"
						)
				)
				.collect::<std::result::Result<Vec<_>, _>>()?;
			let r = Layout::<Blake2Hasher>::ordered_trie_root(values.into_iter());
			context.write_memory(result, &r[..])
				.map_err(|_| "Invalid attempt to set memory in ext_blake2_256_enumerated_trie_root")?;
			Ok(())
		}

		ext_chain_id() -> u64 {
			Ok(sp_io::misc::chain_id())
		}

		ext_twox_64(data: Pointer<u8>, len: WordSize, out: Pointer<u8>) {
			let result: [u8; 8] = if len == 0 {
				let hashed = twox_64(&[0u8; 0]);
				hashed
			} else {
				let key = context.read_memory(data, len)
					.map_err(|_| "Invalid attempt to get key in ext_twox_64")?;
				let hashed_key = twox_64(&key);
				hashed_key
			};

			context.write_memory(out, &result)
				.map_err(|_| "Invalid attempt to set result in ext_twox_64")?;
			Ok(())
		}

		ext_twox_128(data: Pointer<u8>, len: WordSize, out: Pointer<u8>) {
			let result: [u8; 16] = if len == 0 {
				let hashed = twox_128(&[0u8; 0]);
				hashed
			} else {
				let key = context.read_memory(data, len)
					.map_err(|_| "Invalid attempt to get key in ext_twox_128")?;
				let hashed_key = twox_128(&key);
				hashed_key
			};

			context.write_memory(out, &result)
				.map_err(|_| "Invalid attempt to set result in ext_twox_128")?;
			Ok(())
		}

		ext_twox_256(data: Pointer<u8>, len: WordSize, out: Pointer<u8>) {
			let result: [u8; 32] = if len == 0 {
				twox_256(&[0u8; 0])
			} else {
				let mem = context.read_memory(data, len)
					.map_err(|_| "Invalid attempt to get data in ext_twox_256")?;
				twox_256(&mem)
			};
			context.write_memory(out, &result)
				.map_err(|_| "Invalid attempt to set result in ext_twox_256")?;
			Ok(())
		}

		ext_blake2_128(data: Pointer<u8>, len: WordSize, out: Pointer<u8>) {
			let result: [u8; 16] = if len == 0 {
				let hashed = blake2_128(&[0u8; 0]);
				hashed
			} else {
				let key = context.read_memory(data, len)
					.map_err(|_| "Invalid attempt to get key in ext_blake2_128")?;
				let hashed_key = blake2_128(&key);
				hashed_key
			};

			context.write_memory(out, &result)
				.map_err(|_| "Invalid attempt to set result in ext_blake2_128")?;
			Ok(())
		}

		ext_blake2_256(data: Pointer<u8>, len: WordSize, out: Pointer<u8>) {
			let result: [u8; 32] = if len == 0 {
				blake2_256(&[0u8; 0])
			} else {
				let mem = context.read_memory(data, len)
					.map_err(|_| "Invalid attempt to get data in ext_blake2_256")?;
				blake2_256(&mem)
			};
			context.write_memory(out, &result)
				.map_err(|_| "Invalid attempt to set result in ext_blake2_256")?;
			Ok(())
		}

		ext_keccak_256(data: Pointer<u8>, len: WordSize, out: Pointer<u8>) {
			let result: [u8; 32] = if len == 0 {
				keccak_256(&[0u8; 0])
			} else {
				let mem = context.read_memory(data, len)
					.map_err(|_| "Invalid attempt to get data in ext_keccak_256")?;
				keccak_256(&mem)
			};
			context.write_memory(out, &result)
				.map_err(|_| "Invalid attempt to set result in ext_keccak_256")?;
			Ok(())
		}

		ext_ed25519_public_keys(id_data: Pointer<u8>, result_len: Pointer<u32>) -> Pointer<u8> {
			let mut id = [0u8; 4];
			context.read_memory_into(id_data, &mut id[..])
				.map_err(|_| "Invalid attempt to get id in ext_ed25519_public_keys")?;
			let key_type = KeyTypeId(id);

			let keys = sp_io::crypto::ed25519_public_keys(key_type).encode();

			let len = keys.len() as u32;
			let offset = context.allocate_memory(len)?;

			context.write_memory(offset, keys.as_ref())
				.map_err(|_| "Invalid attempt to set memory in ext_ed25519_public_keys")?;
			context.write_primitive(result_len, len)
				.map_err(|_| "Invalid attempt to write result_len in ext_ed25519_public_keys")?;

			Ok(offset)
		}

		ext_ed25519_verify(
			msg_data: Pointer<u8>,
			msg_len: WordSize,
			sig_data: Pointer<u8>,
			pubkey_data: Pointer<u8>,
		) -> u32 {
			let mut sig = [0u8; 64];
			context.read_memory_into(sig_data, &mut sig[..])
				.map_err(|_| "Invalid attempt to get signature in ext_ed25519_verify")?;
			let mut pubkey = [0u8; 32];
			context.read_memory_into(pubkey_data, &mut pubkey[..])
				.map_err(|_| "Invalid attempt to get pubkey in ext_ed25519_verify")?;
			let msg = context.read_memory(msg_data, msg_len)
				.map_err(|_| "Invalid attempt to get message in ext_ed25519_verify")?;

			Ok(if ed25519::Pair::verify_weak(&sig, &msg, &pubkey) {
				0
			} else {
				1
			})
		}

		ext_ed25519_generate(
			id_data: Pointer<u8>,
			seed: Pointer<u8>,
			seed_len: WordSize,
			out: Pointer<u8>,
		) {
			let mut id = [0u8; 4];
			context.read_memory_into(id_data, &mut id[..])
				.map_err(|_| "Invalid attempt to get id in ext_ed25519_generate")?;
			let key_type = KeyTypeId(id);

			let seed = if seed_len == 0 {
				None
			} else {
				Some(
					context.read_memory(seed, seed_len)
						.map_err(|_| "Invalid attempt to get seed in ext_ed25519_generate")?
				)
			};

			let pubkey = sp_io::crypto::ed25519_generate(key_type, seed);

			context.write_memory(out, pubkey.as_ref())
				.map_err(|_| "Invalid attempt to set out in ext_ed25519_generate".into())
		}

		ext_ed25519_sign(
			id_data: Pointer<u8>,
			pubkey_data: Pointer<u8>,
			msg_data: Pointer<u8>,
			msg_len: WordSize,
			out: Pointer<u8>,
		) -> u32 {
			let mut id = [0u8; 4];
			context.read_memory_into(id_data, &mut id[..])
				.map_err(|_| "Invalid attempt to get id in ext_ed25519_sign")?;
			let key_type = KeyTypeId(id);

			let mut pubkey = [0u8; 32];
			context.read_memory_into(pubkey_data, &mut pubkey[..])
				.map_err(|_| "Invalid attempt to get pubkey in ext_ed25519_sign")?;

			let msg = context.read_memory(msg_data, msg_len)
				.map_err(|_| "Invalid attempt to get message in ext_ed25519_sign")?;

			let pub_key = ed25519::Public::try_from(pubkey.as_ref())
				.map_err(|_| "Invalid `ed25519` public key")?;

			let signature = sp_io::crypto::ed25519_sign(key_type, &pub_key, &msg);

			match signature {
				Some(signature) => {
					context.write_memory(out, signature.as_ref())
						.map_err(|_| "Invalid attempt to set out in ext_ed25519_sign")?;
					Ok(0)
				},
				None => Ok(1),
			}
		}

		ext_sr25519_public_keys(id_data: Pointer<u8>, result_len: Pointer<u32>) -> Pointer<u8> {
			let mut id = [0u8; 4];
			context.read_memory_into(id_data, &mut id[..])
				.map_err(|_| "Invalid attempt to get id in ext_sr25519_public_keys")?;
			let key_type = KeyTypeId(id);

			let keys = sp_io::crypto::sr25519_public_keys(key_type).encode();

			let len = keys.len() as u32;
			let offset = context.allocate_memory(len)?;

			context.write_memory(offset, keys.as_ref())
				.map_err(|_| "Invalid attempt to set memory in ext_sr25519_public_keys")?;
			context.write_primitive(result_len, len)
				.map_err(|_| "Invalid attempt to write result_len in ext_sr25519_public_keys")?;

			Ok(offset)
		}

		ext_sr25519_verify(
			msg_data: Pointer<u8>,
			msg_len: WordSize,
			sig_data: Pointer<u8>,
			pubkey_data: Pointer<u8>,
		) -> u32 {
			let mut sig = [0u8; 64];
			context.read_memory_into(sig_data, &mut sig[..])
				.map_err(|_| "Invalid attempt to get signature in ext_sr25519_verify")?;
			let mut pubkey = [0u8; 32];
			context.read_memory_into(pubkey_data, &mut pubkey[..])
				.map_err(|_| "Invalid attempt to get pubkey in ext_sr25519_verify")?;
			let msg = context.read_memory(msg_data, msg_len)
				.map_err(|_| "Invalid attempt to get message in ext_sr25519_verify")?;

			Ok(if sr25519::Pair::verify_weak(&sig, &msg, &pubkey) {
				0
			} else {
				1
			})
		}

		ext_sr25519_generate(
			id_data: Pointer<u8>,
			seed: Pointer<u8>,
			seed_len: WordSize,
			out: Pointer<u8>,
		) {
			let mut id = [0u8; 4];
			context.read_memory_into(id_data, &mut id[..])
				.map_err(|_| "Invalid attempt to get id in ext_sr25519_generate")?;
			let key_type = KeyTypeId(id);
			let seed = if seed_len == 0 {
				None
			} else {
				Some(
					context.read_memory(seed, seed_len)
						.map_err(|_| "Invalid attempt to get seed in ext_sr25519_generate")?
				)
			};

			let pubkey = sp_io::crypto::sr25519_generate(key_type, seed);

			context.write_memory(out, pubkey.as_ref())
				.map_err(|_| "Invalid attempt to set out in ext_sr25519_generate".into())
		}

		ext_sr25519_sign(
			id_data: Pointer<u8>,
			pubkey_data: Pointer<u8>,
			msg_data: Pointer<u8>,
			msg_len: WordSize,
			out: Pointer<u8>,
		) -> u32 {
			let mut id = [0u8; 4];
			context.read_memory_into(id_data, &mut id[..])
				.map_err(|_| "Invalid attempt to get id in ext_sr25519_sign")?;
			let key_type = KeyTypeId(id);

			let mut pubkey = [0u8; 32];
			context.read_memory_into(pubkey_data, &mut pubkey[..])
				.map_err(|_| "Invalid attempt to get pubkey in ext_sr25519_sign")?;

			let msg = context.read_memory(msg_data, msg_len)
				.map_err(|_| "Invalid attempt to get message in ext_sr25519_sign")?;

			let pub_key = sr25519::Public::try_from(pubkey.as_ref())
				.map_err(|_| "Invalid `sr25519` public key")?;

			let signature = sp_io::crypto::sr25519_sign(key_type, &pub_key, &msg);

			match signature {
				Some(signature) => {
					context.write_memory(out, signature.as_ref())
						.map_err(|_| "Invalid attempt to set out in ext_sr25519_sign")?;
					Ok(0)
				},
				None => Ok(1),
			}
		}

		ext_secp256k1_ecdsa_recover(
			msg_data: Pointer<u8>,
			sig_data: Pointer<u8>,
			pubkey_data: Pointer<u8>,
		) -> u32 {
			match secp256k1_recover(context, msg_data, sig_data)? {
				RecoverResult::Invalid(c) => Ok(c),
				RecoverResult::Valid(pubkey) => {
					context.write_memory(pubkey_data, &pubkey.serialize()[1..65])
						.map_err(|_| "Invalid attempt to set pubkey in ext_secp256k1_ecdsa_recover")?;
					Ok(0)
				}
			}
		}

		ext_secp256k1_ecdsa_recover_compressed(
			msg_data: Pointer<u8>,
			sig_data: Pointer<u8>,
			pubkey_data: Pointer<u8>,
		) -> u32 {
			match secp256k1_recover(context, msg_data, sig_data)? {
				RecoverResult::Invalid(c) => Ok(c),
				RecoverResult::Valid(pubkey) => {
					context.write_memory(pubkey_data, &pubkey.serialize_compressed()[..])
						.map_err(|_| "Invalid attempt to set pubkey in ext_secp256k1_ecdsa_recover")?;
					Ok(0)
				}
			}
		}

		ext_is_validator() -> u32 {
			if sp_io::offchain::is_validator() { Ok(1) } else { Ok(0) }
		}

		ext_submit_transaction(msg_data: Pointer<u8>, len: WordSize) -> u32 {
			let extrinsic = context.read_memory(msg_data, len)
				.map_err(|_| "OOB while ext_submit_transaction: wasm")?;

			let res = sp_io::offchain::submit_transaction(extrinsic);

			Ok(if res.is_ok() { 0 } else { 1 })
		}

		ext_network_state(written_out: Pointer<u32>) -> Pointer<u8> {
			let res = sp_io::offchain::network_state();

			let encoded = res.encode();
			let len = encoded.len() as u32;
			let offset = context.allocate_memory(len)?;
			context.write_memory(offset, &encoded)
				.map_err(|_| "Invalid attempt to set memory in ext_network_state")?;

			context.write_primitive(written_out, len)
				.map_err(|_| "Invalid attempt to write written_out in ext_network_state")?;

			Ok(offset)
		}

		ext_timestamp() -> u64 {
			Ok(sp_io::offchain::timestamp().unix_millis())
		}

		ext_sleep_until(deadline: u64) {
			sp_io::offchain::sleep_until(offchain::Timestamp::from_unix_millis(deadline));
			Ok(())
		}

		ext_random_seed(seed_data: Pointer<u8>) {
			// NOTE the runtime as assumptions about seed size.
			let seed = sp_io::offchain::random_seed();

			context.write_memory(seed_data, &seed)
				.map_err(|_| "Invalid attempt to set value in ext_random_seed")?;
			Ok(())
		}

		ext_local_storage_set(
			kind: u32,
			key: Pointer<u8>,
			key_len: WordSize,
			value: Pointer<u8>,
			value_len: WordSize,
		) {
			let kind = offchain::StorageKind::try_from(kind)
					.map_err(|_| "storage kind OOB while ext_local_storage_set: wasm")?;
			let key = context.read_memory(key, key_len)
				.map_err(|_| "OOB while ext_local_storage_set: wasm")?;
			let value = context.read_memory(value, value_len)
				.map_err(|_| "OOB while ext_local_storage_set: wasm")?;

			sp_io::offchain::local_storage_set(kind, &key, &value);

			Ok(())
		}

		ext_local_storage_get(
			kind: u32,
			key: Pointer<u8>,
			key_len: WordSize,
			value_len: Pointer<u32>,
		) -> Pointer<u8> {
			let kind = offchain::StorageKind::try_from(kind)
					.map_err(|_| "storage kind OOB while ext_local_storage_get: wasm")?;
			let key = context.read_memory(key, key_len)
				.map_err(|_| "OOB while ext_local_storage_get: wasm")?;

			let maybe_value = sp_io::offchain::local_storage_get(kind, &key);

			let (offset, len) = if let Some(value) = maybe_value {
				let offset = context.allocate_memory(value.len() as u32)?;
				context.write_memory(offset, &value)
					.map_err(|_| "Invalid attempt to set memory in ext_local_storage_get")?;
				(offset, value.len() as u32)
			} else {
				(Pointer::null(), u32::max_value())
			};

			context.write_primitive(value_len, len)
				.map_err(|_| "Invalid attempt to write value_len in ext_local_storage_get")?;

			Ok(offset)
		}

		ext_local_storage_compare_and_set(
			kind: u32,
			key: Pointer<u8>,
			key_len: WordSize,
			old_value: Pointer<u8>,
			old_value_len: WordSize,
			new_value: Pointer<u8>,
			new_value_len: WordSize,
		) -> u32 {
			let kind = offchain::StorageKind::try_from(kind)
					.map_err(|_| "storage kind OOB while ext_local_storage_compare_and_set: wasm")?;
			let key = context.read_memory(key, key_len)
				.map_err(|_| "OOB while ext_local_storage_compare_and_set: wasm")?;
			let new_value = context.read_memory(new_value, new_value_len)
				.map_err(|_| "OOB while ext_local_storage_compare_and_set: wasm")?;

			let old_value = if old_value_len == u32::max_value() {
				None
			} else {
				Some(
					context.read_memory(old_value, old_value_len)
					.map_err(|_| "OOB while ext_local_storage_compare_and_set: wasm")?
				)
			};

			let res = sp_io::offchain::local_storage_compare_and_set(
				kind,
				&key,
				old_value,
				&new_value,
			);

			Ok(if res { 0 } else { 1 })
		}

		ext_http_request_start(
			method: Pointer<u8>,
			method_len: WordSize,
			url: Pointer<u8>,
			url_len: WordSize,
			meta: Pointer<u8>,
			meta_len: WordSize,
		) -> u32 {
			let method = context.read_memory(method, method_len)
				.map_err(|_| "OOB while ext_http_request_start: wasm")?;
			let url = context.read_memory(url, url_len)
				.map_err(|_| "OOB while ext_http_request_start: wasm")?;
			let meta = context.read_memory(meta, meta_len)
				.map_err(|_| "OOB while ext_http_request_start: wasm")?;

			let method_str = str::from_utf8(&method)
				.map_err(|_| "invalid str while ext_http_request_start: wasm")?;
			let url_str = str::from_utf8(&url)
				.map_err(|_| "invalid str while ext_http_request_start: wasm")?;

			let id = sp_io::offchain::http_request_start(method_str, url_str, &meta);

			if let Ok(id) = id {
				Ok(id.into())
			} else {
				Ok(u32::max_value())
			}
		}

		ext_http_request_add_header(
			request_id: u32,
			name: Pointer<u8>,
			name_len: WordSize,
			value: Pointer<u8>,
			value_len: WordSize,
		) -> u32 {
			let name = context.read_memory(name, name_len)
				.map_err(|_| "OOB while ext_http_request_add_header: wasm")?;
			let value = context.read_memory(value, value_len)
				.map_err(|_| "OOB while ext_http_request_add_header: wasm")?;

			let name_str = str::from_utf8(&name)
				.map_err(|_| "Invalid str while ext_http_request_add_header: wasm")?;
			let value_str = str::from_utf8(&value)
				.map_err(|_| "Invalid str while ext_http_request_add_header: wasm")?;

			let res = sp_io::offchain::http_request_add_header(
				offchain::HttpRequestId(request_id as u16),
				name_str,
				value_str,
			);

			Ok(if res.is_ok() { 0 } else { 1 })
		}

		ext_http_request_write_body(
			request_id: u32,
			chunk: Pointer<u8>,
			chunk_len: WordSize,
			deadline: u64,
		) -> u32 {
			let chunk = context.read_memory(chunk, chunk_len)
				.map_err(|_| "OOB while ext_http_request_write_body: wasm")?;

			let res = sp_io::offchain::http_request_write_body(
				offchain::HttpRequestId(request_id as u16),
				&chunk,
				deadline_to_timestamp(deadline),
			);

			Ok(match res {
				Ok(()) => 0,
				Err(e) => e.into(),
			})
		}

		ext_http_response_wait(
			ids: Pointer<u32>,
			ids_len: WordSize,
			statuses: Pointer<u32>,
			deadline: u64,
		) {
			let ids = (0..ids_len)
				.map(|i|
					 context.read_primitive(ids.offset(i).ok_or("Point overflow")?)
						.map(|id: u32| offchain::HttpRequestId(id as u16))
						.map_err(|_| "OOB while ext_http_response_wait: wasm")
				)
				.collect::<std::result::Result<Vec<_>, _>>()?;

			let res = sp_io::offchain::http_response_wait(&ids, deadline_to_timestamp(deadline))
				.into_iter()
				.map(|status| u32::from(status))
				.enumerate()
				// make sure to take up to `ids_len` to avoid exceeding the mem.
				.take(ids_len as usize);

			for (i, status) in res {
				context.write_primitive(statuses.offset(i as u32).ok_or("Point overflow")?, status)
					.map_err(|_| "Invalid attempt to set memory in ext_http_response_wait")?;
			}

			Ok(())
		}

		ext_http_response_headers(
			request_id: u32,
			written_out: Pointer<u32>,
		) -> Pointer<u8> {
			use codec::Encode;

			let headers = sp_io::offchain::http_response_headers(
				offchain::HttpRequestId(request_id as u16),
			);

			let encoded = headers.encode();
			let len = encoded.len() as u32;
			let offset = context.allocate_memory(len)?;

			context.write_memory(offset, &encoded)
				.map_err(|_| "Invalid attempt to set memory in ext_http_response_headers")?;
			context.write_primitive(written_out, len)
				.map_err(|_| "Invalid attempt to write written_out in ext_http_response_headers")?;

			Ok(offset)
		}

		ext_http_response_read_body(
			request_id: u32,
			buffer: Pointer<u8>,
			buffer_len: WordSize,
			deadline: u64,
		) -> WordSize {
			let mut internal_buffer = Vec::with_capacity(buffer_len as usize);
			internal_buffer.resize(buffer_len as usize, 0);

			let res = sp_io::offchain::http_response_read_body(
				offchain::HttpRequestId(request_id as u16),
				&mut internal_buffer,
				deadline_to_timestamp(deadline),
			);

			Ok(match res {
				Ok(read) => {
					context.write_memory(buffer, &internal_buffer[..read as usize])
						.map_err(|_| "Invalid attempt to set memory in ext_http_response_read_body")?;

					read as u32
				},
				Err(err) => {
					u32::max_value() - u32::from(err) + 1
				}
			})
		}
	}
}

fn deadline_to_timestamp(deadline: u64) -> Option<offchain::Timestamp> {
	if deadline == 0 {
		None
	} else {
		Some(offchain::Timestamp::from_unix_millis(deadline))
	}
}
