// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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
