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
