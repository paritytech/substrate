// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Polkadot Blake2b Hasher implementation

use hashdb::Hasher;
use plain_hasher::PlainHasher;
use hash::H256;
use hashing::blake2_256;

/// Concrete implementation of Hasher using Blake2b 256-bit hashes
pub struct BlakeHasher;
impl Hasher for BlakeHasher {
	type Out = H256;
	type StdHasher = PlainHasher;
	const LENGTH:usize = 32;
	fn hash(x: &[u8]) -> Self::Out {
		blake2_256(x).into()
	}
}
