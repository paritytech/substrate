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

use pow_primitives::{Difficulty, Seal as RawSeal};
use primitives::{H256, U256};
use runtime_io::blake2_256;
use codec::{Encode, Decode};

fn verify_difficulty(hash: &H256, difficulty: Difficulty, proportion: Difficulty) -> bool {
	let target = U256::from(difficulty) * U256::from(proportion);
	let seal = U256::from(&hash[..]);

	seal > target
}

#[derive(Clone, PartialEq, Eq, Encode, Decode)]
pub struct Seal {
	pub nonce: H256,
	pub work: H256,
}

pub fn verify(
	pre_hash: &H256,
	seal: &RawSeal,
	difficulty: Difficulty,
	proportion: Difficulty
) -> bool {
	let seal = match Seal::decode(&mut &seal[..]) {
		Ok(seal) => seal,
		Err(_) => return false,
	};

	if H256::from(blake2_256(&(pre_hash, seal.nonce).encode())) != seal.work {
		return false
	}

	if !verify_difficulty(&seal.work, difficulty, proportion) {
		return false
	}

	true
}

pub fn mine(
	pre_hash: &H256,
	seed: &H256,
	difficulty: Difficulty,
	round: u32,
	proportion: Difficulty,
) -> Option<RawSeal> {
	for i in 0..round {
		let nonce = {
			let mut ret = H256::default();
			(U256::from(&seed[..]) + U256::from(i)).to_big_endian(&mut ret[..]);
			ret
		};
		let work = H256::from(blake2_256(&(pre_hash, nonce).encode()));

		if verify_difficulty(&work, difficulty, proportion) {
			return Some(Seal { nonce, work }.encode())
		}
	}

	None
}
