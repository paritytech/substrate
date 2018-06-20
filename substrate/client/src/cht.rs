// TODO: get rid of ok()

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

//! Canonical hash trie definitions and helper functions.
//!
//! Each CHT is a trie mapping block numbers to canonical hash.
//! One is generated for every `SIZE` blocks, allowing us to discard those blocks in
//! favor of the trie root. When the "ancient" blocks need to be accessed, we simply
//! request an inclusion proof of a specific block number against the trie with the
//! root has. A correct proof implies that the claimed block is identical to the one
//! we discarded.

use triehash;

use primitives::block::{HeaderHash, Number as BlockNumber};
use state_machine::backend::InMemory as InMemoryState;
use state_machine::{prove_read, read_proof_check};

use error::{Error as ClientError, ErrorKind as ClientErrorKind, Result as ClientResult};

/// The size of each CHT.
pub const SIZE: BlockNumber = 2048;

/// Returns Some(cht_number) if CHT is need to be built when the block with given number is canonized.
pub fn is_build_required(block_num: BlockNumber) -> Option<BlockNumber> {
	let block_cht_num = block_to_cht_number(block_num)?;
	if block_cht_num < 2 {
		return None;
	}
	let cht_start = start_number(block_cht_num);
	if cht_start != block_num {
		return None;
	}

	Some(block_cht_num - 2)
}

/// Compute a CHT root from an iterator of block hashes. Fails if shorter than
/// SIZE items. The items are assumed to proceed sequentially from `start_number(cht_num)`.
/// Discards the trie's nodes.
pub fn compute_root<I: IntoIterator<Item=Option<HeaderHash>>>(cht_num: BlockNumber, hashes: I) -> Option<HeaderHash> {
	build_pairs(cht_num, hashes).map(|pairs| triehash::trie_root(pairs).0.into())
}

/// Build CHT-based header proof.
pub fn build_proof<I: IntoIterator<Item=Option<HeaderHash>>>(cht_num: BlockNumber, block_num: BlockNumber, hashes: I) -> Option<Vec<Vec<u8>>> {
	let transaction = build_pairs(cht_num, hashes)?
		.into_iter()
		.map(|(k, v)| (k, Some(v)))
		.collect::<Vec<_>>();
	let storage = InMemoryState::default().update(transaction);
	let (value, proof) = prove_read(storage, &encode_cht_key(block_num)).ok()?;
	if value.is_none() {
		return None;
		//return Err(ClientErrorKind::InvalidHeaderProof.into());
	}
	Some(proof)
}

/// Check CHT-based header proof.
pub fn check_proof(local_root: HeaderHash, local_number: BlockNumber, remote_hash: HeaderHash, remote_proof: Vec<Vec<u8>>) -> ClientResult<()> {
	let local_cht_key = encode_cht_key(local_number);
	let local_cht_value = read_proof_check(local_root.into(), remote_proof, &local_cht_key).map_err(|e| ClientError::from(e))?;
	let local_cht_value = local_cht_value.ok_or_else(|| ClientErrorKind::InvalidHeaderProof)?;
	let local_hash = decode_cht_value(&local_cht_value);
	match local_hash == remote_hash {
		true => Ok(()),
		false => Err(ClientErrorKind::InvalidHeaderProof.into()),
	}
}

/// Build CHT.
fn build_pairs<I: IntoIterator<Item=Option<HeaderHash>>>(cht_num: BlockNumber, hashes: I) -> Option<Vec<(Vec<u8>, Vec<u8>)>> {
	let start_num = start_number(cht_num);
	let pairs = hashes.into_iter()
		.take(SIZE as usize)
		.enumerate()
		.filter_map(|(i, hash)| hash.map(|hash| (
			encode_cht_key(start_num + i as BlockNumber).to_vec(),
			encode_cht_value(hash)
		)))
		.collect::<Vec<_>>();
	match pairs.len() == SIZE as usize {
		true => Some(pairs),
		false => None,
	}
}

/// Get the starting block of a given CHT.
/// CHT 0 includes block 1...SIZE,
/// CHT 1 includes block SIZE + 1 ... 2*SIZE
/// More generally: CHT N includes block (1 + N*SIZE)...((N+1)*SIZE).
/// This is because the genesis hash is assumed to be known
/// and including it would be redundant.
pub fn start_number(cht_num: BlockNumber) -> BlockNumber {
	(cht_num * SIZE) + 1
}

/// Get the ending block of a given CHT.
pub fn end_number(cht_num: BlockNumber) -> BlockNumber {
	(cht_num + 1) * SIZE
}

/// Convert a block number to a CHT number.
/// Returns `None` for `block_num` == 0, `Some` otherwise.
pub fn block_to_cht_number(block_num: BlockNumber) -> Option<BlockNumber> {
	match block_num {
		0 => None,
		n => Some((n - 1) / SIZE),
	}
}

/// Convert header number into CHT key.
pub fn encode_cht_key(number: BlockNumber) -> Vec<u8> {
	vec![
		(number >> 24) as u8,
		((number >> 16) & 0xff) as u8,
		((number >> 8) & 0xff) as u8,
		(number & 0xff) as u8
	]
}

/// Convert header hast into CHT value.
fn encode_cht_value(hash: HeaderHash) -> Vec<u8> {
	hash.to_vec()
}

/// Convert CHT value into block header hash.
pub fn decode_cht_value(value: &[u8]) -> HeaderHash {
	value.into()
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn is_build_required_works() {
		assert_eq!(is_build_required(0), None);
		assert_eq!(is_build_required(1), None);
		assert_eq!(is_build_required(SIZE), None);
		assert_eq!(is_build_required(SIZE + 1), None);
		assert_eq!(is_build_required(2 * SIZE), None);
		assert_eq!(is_build_required(2 * SIZE + 1), Some(0));
		assert_eq!(is_build_required(3 * SIZE), None);
		assert_eq!(is_build_required(3 * SIZE + 1), Some(1));
	}

	#[test]
	fn start_number_works() {
		assert_eq!(start_number(0), 1);
		assert_eq!(start_number(1), SIZE + 1);
		assert_eq!(start_number(2), SIZE + SIZE + 1);
	}

	#[test]
	fn end_number_works() {
		assert_eq!(end_number(0), SIZE);
		assert_eq!(end_number(1), SIZE + SIZE);
		assert_eq!(end_number(2), SIZE + SIZE + SIZE);
	}

	#[test]
	fn build_pairs_fails_when_no_enough_blocks() {
		assert!(build_pairs(0, vec![Some(1.into()); SIZE as usize / 2]).is_none());
	}

	#[test]
	fn build_pairs_fails_when_missing_block() {
		assert!(build_pairs(0, ::std::iter::repeat(Some(1.into())).take(SIZE as usize / 2)
			.chain(::std::iter::once(None))
			.chain(::std::iter::repeat(Some(2.into())).take(SIZE as usize / 2 - 1))).is_none());
	}

	#[test]
	fn compute_root_works() {
		assert!(compute_root(42, vec![Some(1.into()); SIZE as usize]).is_some());
	}

	#[test]
	fn build_proof_fails_when_querying_wrong_block() {
		assert!(build_proof(0, SIZE * 1000, vec![Some(1.into()); SIZE as usize]).is_none());
	}

	#[test]
	fn build_proof_works() {
		assert!(build_proof(0, SIZE / 2, vec![Some(1.into()); SIZE as usize]).is_some());
	}
}
