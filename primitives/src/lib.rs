// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Shareable Polkadot types.

#![warn(missing_docs)]

extern crate rustc_hex;
extern crate serde;
extern crate ring;
extern crate untrusted;
extern crate twox_hash;
extern crate byteorder;
extern crate blake2_rfc;

#[macro_use]
extern crate crunchy;
#[macro_use]
extern crate fixed_hash;
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate uint as uint_crate;

#[cfg(feature="std")]
extern crate core;
#[cfg(test)]
extern crate polkadot_serializer;
#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;

mod bytes;
pub mod block;
pub mod contract;
pub mod hash;
pub mod parachain;
pub mod uint;
pub mod validator;
pub mod ed25519;

/// Alias to 160-bit hash when used in the context of an account address.
pub type Address = hash::H160;
/// Alias to 520-bit hash when used in the context of a signature.
pub type Signature = hash::H512;

pub use self::hash::{H160, H256};
pub use self::uint::{U256, U512};

/// A hash function.
pub fn hash(data: &[u8]) -> hash::H256 {
	blake2_256(data).into()
}

/// Do a Blake2 512-bit hash and place result in `dest`.
pub fn blake2_512_into(data: &[u8], dest: &mut[u8; 64]) {
	dest.copy_from_slice(blake2_rfc::blake2b::blake2b(64, &[], data).as_bytes());
}

/// Do a Blake2 512-bit hash and return result.
pub fn blake2_512(data: &[u8]) -> [u8; 64] {
	let mut r: [u8; 64] = unsafe { std::mem::uninitialized() };
	blake2_512_into(data, &mut r);
	r
}

/// Do a Blake2 256-bit hash and place result in `dest`.
pub fn blake2_256_into(data: &[u8], dest: &mut[u8; 32]) {
	dest.copy_from_slice(blake2_rfc::blake2b::blake2b(32, &[], data).as_bytes());
}

/// Do a Blake2 256-bit hash and return result.
pub fn blake2_256(data: &[u8]) -> [u8; 32] {
	let mut r: [u8; 32] = unsafe { std::mem::uninitialized() };
	blake2_256_into(data, &mut r);
	r
}

/// Do a Blake2 128-bit hash and place result in `dest`.
pub fn blake2_128_into(data: &[u8], dest: &mut[u8; 16]) {
	dest.copy_from_slice(blake2_rfc::blake2b::blake2b(16, &[], data).as_bytes());
}

/// Do a Blake2 128-bit hash and return result.
pub fn blake2_128(data: &[u8]) -> [u8; 16] {
	let mut r: [u8; 16] = unsafe { std::mem::uninitialized() };
	blake2_128_into(data, &mut r);
	r
}

/// Do a XX 128-bit hash and place result in `dest`.
pub fn twox_128_into(data: &[u8], dest: &mut [u8; 16]) {
	use ::std::hash::Hasher;
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
	let mut r: [u8; 16] = unsafe { std::mem::uninitialized() };
	twox_128_into(data, &mut r);
	r
}

/// Do a XX 256-bit hash and place result in `dest`.
pub fn twox_256_into(data: &[u8], dest: &mut [u8; 32]) {
	use ::std::hash::Hasher;
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
	let mut r: [u8; 32] = unsafe { std::mem::uninitialized() };
	twox_256_into(data, &mut r);
	r
}
