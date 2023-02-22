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

//! Hashing functions.
//!
//! This module is gated by `full-crypto` feature. If you intend to use any of the functions
//! defined here within your runtime, you should most likely rather use `sp_io::hashing` instead,
//! unless you know what you're doing. Using `sp_io` will be more performant, since instead of
//! computing the hash in WASM it delegates that computation to the host client.

pub use sp_core_hashing::*;

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn blake2b() {
		assert_eq!(sp_core_hashing_proc_macro::blake2b_64!(b""), blake2_64(b"")[..]);
		assert_eq!(sp_core_hashing_proc_macro::blake2b_256!(b"test"), blake2_256(b"test")[..]);
		assert_eq!(sp_core_hashing_proc_macro::blake2b_512!(b""), blake2_512(b"")[..]);
	}

	#[test]
	fn keccak() {
		assert_eq!(sp_core_hashing_proc_macro::keccak_256!(b"test"), keccak_256(b"test")[..]);
		assert_eq!(sp_core_hashing_proc_macro::keccak_512!(b"test"), keccak_512(b"test")[..]);
	}

	#[test]
	fn sha2() {
		assert_eq!(sp_core_hashing_proc_macro::sha2_256!(b"test"), sha2_256(b"test")[..]);
	}

	#[test]
	fn twox() {
		assert_eq!(sp_core_hashing_proc_macro::twox_128!(b"test"), twox_128(b"test")[..]);
		assert_eq!(sp_core_hashing_proc_macro::twox_64!(b""), twox_64(b"")[..]);
	}

	#[test]
	fn twox_concats() {
		assert_eq!(
			sp_core_hashing_proc_macro::twox_128!(b"test", b"123", b"45", b"", b"67890"),
			super::twox_128(&b"test1234567890"[..]),
		);
		assert_eq!(
			sp_core_hashing_proc_macro::twox_128!(b"test", test, b"45", b"", b"67890"),
			super::twox_128(&b"testtest4567890"[..]),
		);
	}
}
