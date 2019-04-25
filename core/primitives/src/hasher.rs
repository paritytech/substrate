// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Substrate Blake2b Hasher implementation

use hash_db::Hasher;
use hash256_std_hasher::Hash256StdHasher;
use crate::hash::H256;

pub mod blake2 {
	use super::{Hasher, Hash256StdHasher, H256};
	#[cfg(feature = "std")]
	use crate::hashing::blake2_256;

	#[cfg(not(feature = "std"))]
	extern "C" {
		fn ext_blake2_256(data: *const u8, len: u32, out: *mut u8);
	}
	#[cfg(not(feature = "std"))]
	fn blake2_256(data: &[u8]) -> [u8; 32] {
		let mut result: [u8; 32] = Default::default();
		unsafe {
			ext_blake2_256(data.as_ptr(), data.len() as u32, result.as_mut_ptr());
		}
		result
	}

	/// Concrete implementation of Hasher using Blake2b 256-bit hashes
	#[derive(Debug)]
	pub struct Blake2Hasher;

	impl Hasher for Blake2Hasher {
		type Out = H256;
		type StdHasher = Hash256StdHasher;
		const LENGTH: usize = 32;
		fn hash(x: &[u8]) -> Self::Out {
			blake2_256(x).into()
		}
	}
}
