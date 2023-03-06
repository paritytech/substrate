// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Hashing Functions.

#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

use core::hash::Hasher;

use byteorder::{ByteOrder, LittleEndian};
use digest::{
	consts::{U16, U32, U8},
	Digest,
};

/// Do a Blake2 512-bit hash and place result in `dest`.
pub fn blake2_512_into(data: &[u8], dest: &mut [u8; 64]) {
	dest.copy_from_slice(blake2::Blake2b512::digest(data).as_slice());
}

/// Do a Blake2 512-bit hash and return result.
pub fn blake2_512(data: &[u8]) -> [u8; 64] {
	blake2::Blake2b512::digest(data).into()
}

/// Do a Blake2 256-bit hash and return result.
pub fn blake2_256(data: &[u8]) -> [u8; 32] {
	blake2::Blake2b::<U32>::digest(data).into()
}

/// Do a Blake2 128-bit hash and return result.
pub fn blake2_128(data: &[u8]) -> [u8; 16] {
	blake2::Blake2b::<U16>::digest(data).into()
}

/// Do a Blake2 64-bit hash and return result.
pub fn blake2_64(data: &[u8]) -> [u8; 8] {
	blake2::Blake2b::<U8>::digest(data).into()
}

/// Do a XX 64-bit hash and place result in `dest`.
pub fn twox_64_into(data: &[u8], dest: &mut [u8; 8]) {
	let r0 = twox_hash::XxHash::with_seed(0).chain_update(data).finish();
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
	let r0 = twox_hash::XxHash::with_seed(0).chain_update(data).finish();
	let r1 = twox_hash::XxHash::with_seed(1).chain_update(data).finish();
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
	let r0 = twox_hash::XxHash::with_seed(0).chain_update(data).finish();
	let r1 = twox_hash::XxHash::with_seed(1).chain_update(data).finish();
	let r2 = twox_hash::XxHash::with_seed(2).chain_update(data).finish();
	let r3 = twox_hash::XxHash::with_seed(3).chain_update(data).finish();
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
	sha3::Keccak256::digest(data).into()
}

/// Do a keccak 512-bit hash and return result.
pub fn keccak_512(data: &[u8]) -> [u8; 64] {
	sha3::Keccak512::digest(data).into()
}

/// Do a sha2 256-bit hash and return result.
pub fn sha2_256(data: &[u8]) -> [u8; 32] {
	sha2::Sha256::digest(data).into()
}
