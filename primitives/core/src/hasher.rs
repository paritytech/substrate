// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

//! Substrate Blake2b Hasher implementation

pub mod blake2 {
	use crate::hash::H256;
	use hash256_std_hasher::Hash256StdHasher;
	use hash_db::Hasher;

	/// Concrete implementation of Hasher using Blake2b 256-bit hashes
	#[derive(Debug)]
	pub struct Blake2Hasher;

	impl Hasher for Blake2Hasher {
		type Out = H256;
		type StdHasher = Hash256StdHasher;
		const LENGTH: usize = 32;

		fn hash(x: &[u8]) -> Self::Out {
			crate::hashing::blake2_256(x).into()
		}
	}
}

pub mod keccak {
	use crate::hash::H256;
	use hash256_std_hasher::Hash256StdHasher;
	use hash_db::Hasher;

	/// Concrete implementation of Hasher using Keccak 256-bit hashes
	#[derive(Debug)]
	pub struct KeccakHasher;

	impl Hasher for KeccakHasher {
		type Out = H256;
		type StdHasher = Hash256StdHasher;
		const LENGTH: usize = 32;

		fn hash(x: &[u8]) -> Self::Out {
			crate::hashing::keccak_256(x).into()
		}
	}
}
