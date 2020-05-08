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

//! Hashing functions.

use blake2_rfc;
use sha2::{Digest, Sha256};
use tiny_keccak::{Hasher, Keccak};
use twox_hash;

/// Do a Blake2 512-bit hash and place result in `dest`.
pub fn blake2_512_into(data: &[u8], dest: &mut [u8; 64]) {
	dest.copy_from_slice(blake2_rfc::blake2b::blake2b(64, &[], data).as_bytes());
}

/// Do a Blake2 512-bit hash and return result.
pub fn blake2_512(data: &[u8]) -> [u8; 64] {
	let mut r = [0; 64];
	blake2_512_into(data, &mut r);
	r
}

/// Do a Blake2 256-bit hash and place result in `dest`.
pub fn blake2_256_into(data: &[u8], dest: &mut [u8; 32]) {
	dest.copy_from_slice(blake2_rfc::blake2b::blake2b(32, &[], data).as_bytes());
}

/// Do a Blake2 256-bit hash and return result.
pub fn blake2_256(data: &[u8]) -> [u8; 32] {
	let mut r = [0; 32];
	blake2_256_into(data, &mut r);
	r
}

/// Do a Blake2 128-bit hash and place result in `dest`.
pub fn blake2_128_into(data: &[u8], dest: &mut [u8; 16]) {
	dest.copy_from_slice(blake2_rfc::blake2b::blake2b(16, &[], data).as_bytes());
}

/// Do a Blake2 128-bit hash and return result.
pub fn blake2_128(data: &[u8]) -> [u8; 16] {
	let mut r = [0; 16];
	blake2_128_into(data, &mut r);
	r
}

/// Do a Blake2 64-bit hash and place result in `dest`.
pub fn blake2_64_into(data: &[u8], dest: &mut [u8; 8]) {
	dest.copy_from_slice(blake2_rfc::blake2b::blake2b(8, &[], data).as_bytes());
}

/// Do a Blake2 64-bit hash and return result.
pub fn blake2_64(data: &[u8]) -> [u8; 8] {
	let mut r = [0; 8];
	blake2_64_into(data, &mut r);
	r
}

/// Do a XX 64-bit hash and place result in `dest`.
pub fn twox_64_into(data: &[u8], dest: &mut [u8; 8]) {
	use ::core::hash::Hasher;
	let mut h0 = twox_hash::XxHash::with_seed(0);
	h0.write(data);
	let r0 = h0.finish();
	use byteorder::{ByteOrder, LittleEndian};
	LittleEndian::write_u64(&mut dest[0..8], r0);
}

/// Do a XX 64-bit hash and return result.
pub fn twox_64(data: &[u8]) -> [u8; 8] {
	let mut r: [u8; 8] = [0; 8];
	twox_64_into(data, &mut r);
	r
}

/// Do a XX 128-bit hash and place result in `dest`.
pub fn twox_128_into(data: &[u8], dest: &mut [u8; 16]) {
	use ::core::hash::Hasher;
	let mut h0 = twox_hash::XxHash::with_seed(0);
	let mut h1 = twox_hash::XxHash::with_seed(1);
	h0.write(data);
	h1.write(data);
	let r0 = h0.finish();
	let r1 = h1.finish();
	use byteorder::{ByteOrder, LittleEndian};
	LittleEndian::write_u64(&mut dest[0..8], r0);
	LittleEndian::write_u64(&mut dest[8..16], r1);
}

/// Do a XX 128-bit hash and return result.
pub fn twox_128(data: &[u8]) -> [u8; 16] {
	let mut r: [u8; 16] = [0; 16];
	twox_128_into(data, &mut r);
	r
}

/// Do a XX 256-bit hash and place result in `dest`.
pub fn twox_256_into(data: &[u8], dest: &mut [u8; 32]) {
	use ::core::hash::Hasher;
	use byteorder::{ByteOrder, LittleEndian};
	let mut h0 = twox_hash::XxHash::with_seed(0);
	let mut h1 = twox_hash::XxHash::with_seed(1);
	let mut h2 = twox_hash::XxHash::with_seed(2);
	let mut h3 = twox_hash::XxHash::with_seed(3);
	h0.write(data);
	h1.write(data);
	h2.write(data);
	h3.write(data);
	let r0 = h0.finish();
	let r1 = h1.finish();
	let r2 = h2.finish();
	let r3 = h3.finish();
	LittleEndian::write_u64(&mut dest[0..8], r0);
	LittleEndian::write_u64(&mut dest[8..16], r1);
	LittleEndian::write_u64(&mut dest[16..24], r2);
	LittleEndian::write_u64(&mut dest[24..32], r3);
}

/// Do a XX 256-bit hash and return result.
pub fn twox_256(data: &[u8]) -> [u8; 32] {
	let mut r: [u8; 32] = [0; 32];
	twox_256_into(data, &mut r);
	r
}

/// Do a keccak 256-bit hash and return result.
pub fn keccak_256(data: &[u8]) -> [u8; 32] {
	let mut keccak = Keccak::v256();
	keccak.update(data);
	let mut output = [0u8; 32];
	keccak.finalize(&mut output);
	output
}

/// Do a sha2 256-bit hash and return result.
pub fn sha2_256(data: &[u8]) -> [u8; 32] {
	let mut hasher = Sha256::new();
	hasher.input(data);
	let mut output = [0u8; 32];
	output.copy_from_slice(&hasher.result());
	output
}
