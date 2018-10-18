// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Canonical hash trie definitions and helper functions.
//!
//! Each CHT is a trie mapping block numbers to canonical hash.
//! One is generated for every `SIZE` blocks, allowing us to discard those blocks in
//! favor of the trie root. When the "ancient" blocks need to be accessed, we simply
//! request an inclusion proof of a specific block number against the trie with the
//! root has. A correct proof implies that the claimed block is identical to the one
//! we discarded.

use hash_db;
use heapsize::HeapSizeOf;
use trie;

use primitives::H256;
use runtime_primitives::traits::{As, Header as HeaderT, SimpleArithmetic, One};
use state_machine::backend::InMemory as InMemoryState;
use state_machine::{prove_read, read_proof_check};

use error::{Error as ClientError, ErrorKind as ClientErrorKind, Result as ClientResult};

/// The size of each CHT. This value is passed to every CHT-related function from
/// production code. Other values are passed from tests.
pub const SIZE: u64 = 2048;

/// Returns Some(cht_number) if CHT is need to be built when the block with given number is canonized.
pub fn is_build_required<N>(cht_size: u64, block_num: N) -> Option<N>
	where
		N: Clone + SimpleArithmetic,
{
	let block_cht_num = block_to_cht_number(cht_size, block_num.clone())?;
	let two = N::one() + N::one();
	if block_cht_num < two {
		return None;
	}
	let cht_start = start_number(cht_size, block_cht_num.clone());
	if cht_start != block_num {
		return None;
	}

	Some(block_cht_num - two)
}

/// Compute a CHT root from an iterator of block hashes. Fails if shorter than
/// SIZE items. The items are assumed to proceed sequentially from `start_number(cht_num)`.
/// Discards the trie's nodes.
pub fn compute_root<Header, Hasher, I>(
	cht_size: u64,
	cht_num: Header::Number,
	hashes: I,
) -> Option<Hasher::Out>
	where
		Header: HeaderT,
		Hasher: hash_db::Hasher,
		Hasher::Out: Ord,
		I: IntoIterator<Item=Option<Header::Hash>>,
{
	build_pairs::<Header, I>(cht_size, cht_num, hashes)
		.map(|pairs| trie::trie_root::<Hasher, _, _, _>(pairs))
}

/// Build CHT-based header proof.
pub fn build_proof<Header, Hasher, I>(
	cht_size: u64,
	cht_num: Header::Number,
	block_num: Header::Number,
	hashes: I
) -> Option<Vec<Vec<u8>>>
	where
		Header: HeaderT,
		Hasher: hash_db::Hasher,
		Hasher::Out: Ord + HeapSizeOf,
		I: IntoIterator<Item=Option<Header::Hash>>,
{
	let transaction = build_pairs::<Header, I>(cht_size, cht_num, hashes)?
		.into_iter()
		.map(|(k, v)| (None, k, Some(v)))
		.collect::<Vec<_>>();
	let storage = InMemoryState::<Hasher>::default().update(transaction);
	let (value, proof) = prove_read(storage, &encode_cht_key(block_num)).ok()?;
	if value.is_none() {
		None
	} else {
		Some(proof)
	}
}

/// Check CHT-based header proof.
pub fn check_proof<Header, Hasher>(
	local_root: Header::Hash,
	local_number: Header::Number,
	remote_hash: Header::Hash,
	remote_proof: Vec<Vec<u8>>
) -> ClientResult<()>
	where
		Header: HeaderT,
		Header::Hash: AsRef<[u8]>,
		Hasher: hash_db::Hasher,
		Hasher::Out: Ord + HeapSizeOf,
{
	let mut root: Hasher::Out = Default::default();
	root.as_mut().copy_from_slice(local_root.as_ref());
	let local_cht_key = encode_cht_key(local_number);
	let local_cht_value = read_proof_check::<Hasher>(root, remote_proof,
		&local_cht_key).map_err(|e| ClientError::from(e))?;
	let local_cht_value = local_cht_value.ok_or_else(|| ClientErrorKind::InvalidHeaderProof)?;
	let local_hash = decode_cht_value(&local_cht_value).ok_or_else(|| ClientErrorKind::InvalidHeaderProof)?;
	match &local_hash[..] == remote_hash.as_ref() {
		true => Ok(()),
		false => Err(ClientErrorKind::InvalidHeaderProof.into()),
	}
}

/// Build pairs for computing CHT.
fn build_pairs<Header, I>(
	cht_size: u64,
	cht_num: Header::Number,
	hashes: I
) -> Option<Vec<(Vec<u8>, Vec<u8>)>>
	where
		Header: HeaderT,
		I: IntoIterator<Item=Option<Header::Hash>>,
{
	let start_num = start_number(cht_size, cht_num);
	let mut pairs = Vec::new();
	let mut hash_number = start_num;
	for hash in hashes.into_iter().take(cht_size as usize) {
		pairs.push(hash.map(|hash| (
			encode_cht_key(hash_number).to_vec(),
			encode_cht_value(hash)
		))?);
		hash_number += Header::Number::one();
	}

	if pairs.len() as u64 == cht_size {
		Some(pairs)
	} else {
		None
	}
}

/// Get the starting block of a given CHT.
/// CHT 0 includes block 1...SIZE,
/// CHT 1 includes block SIZE + 1 ... 2*SIZE
/// More generally: CHT N includes block (1 + N*SIZE)...((N+1)*SIZE).
/// This is because the genesis hash is assumed to be known
/// and including it would be redundant.
pub fn start_number<N: SimpleArithmetic>(cht_size: u64, cht_num: N) -> N {
	(cht_num * As::sa(cht_size)) + N::one()
}

/// Get the ending block of a given CHT.
pub fn end_number<N: SimpleArithmetic>(cht_size: u64, cht_num: N) -> N {
	(cht_num + N::one()) * As::sa(cht_size)
}

/// Convert a block number to a CHT number.
/// Returns `None` for `block_num` == 0, `Some` otherwise.
pub fn block_to_cht_number<N: SimpleArithmetic>(cht_size: u64, block_num: N) -> Option<N> {
	if block_num == N::zero() {
		None
	} else {
		Some((block_num - N::one()) / As::sa(cht_size))
	}
}

/// Convert header number into CHT key.
pub fn encode_cht_key<N: As<u64>>(number: N) -> Vec<u8> {
	let number: u64 = number.as_();
	vec![
		(number >> 56) as u8,
		((number >> 48) & 0xff) as u8,
		((number >> 40) & 0xff) as u8,
		((number >> 32) & 0xff) as u8,
		((number >> 24) & 0xff) as u8,
		((number >> 16) & 0xff) as u8,
		((number >> 8) & 0xff) as u8,
		(number & 0xff) as u8
	]
}

/// Convert header hash into CHT value.
fn encode_cht_value<Hash: AsRef<[u8]>>(hash: Hash) -> Vec<u8> {
	hash.as_ref().to_vec()
}

/// Convert CHT value into block header hash.
pub fn decode_cht_value(value: &[u8]) -> Option<H256> {
	match value.len() {
		32 => Some(H256::from_slice(&value[0..32])),
		_ => None,
	}

}

#[cfg(test)]
mod tests {
	use primitives::{Blake2Hasher};
	use test_client::runtime::Header;
	use super::*;

	#[test]
	fn is_build_required_works() {
		assert_eq!(is_build_required(SIZE, 0u64), None);
		assert_eq!(is_build_required(SIZE, 1u64), None);
		assert_eq!(is_build_required(SIZE, SIZE), None);
		assert_eq!(is_build_required(SIZE, SIZE + 1), None);
		assert_eq!(is_build_required(SIZE, 2 * SIZE), None);
		assert_eq!(is_build_required(SIZE, 2 * SIZE + 1), Some(0));
		assert_eq!(is_build_required(SIZE, 3 * SIZE), None);
		assert_eq!(is_build_required(SIZE, 3 * SIZE + 1), Some(1));
	}

	#[test]
	fn start_number_works() {
		assert_eq!(start_number(SIZE, 0u64), 1u64);
		assert_eq!(start_number(SIZE, 1u64), SIZE + 1);
		assert_eq!(start_number(SIZE, 2u64), SIZE + SIZE + 1);
	}

	#[test]
	fn end_number_works() {
		assert_eq!(end_number(SIZE, 0u64), SIZE);
		assert_eq!(end_number(SIZE, 1u64), SIZE + SIZE);
		assert_eq!(end_number(SIZE, 2u64), SIZE + SIZE + SIZE);
	}

	#[test]
	fn build_pairs_fails_when_no_enough_blocks() {
		assert!(build_pairs::<Header, _>(SIZE, 0, vec![Some(1.into()); SIZE as usize / 2]).is_none());
	}

	#[test]
	fn build_pairs_fails_when_missing_block() {
		assert!(build_pairs::<Header, _>(SIZE, 0, ::std::iter::repeat(Some(1.into())).take(SIZE as usize / 2)
			.chain(::std::iter::once(None))
			.chain(::std::iter::repeat(Some(2.into())).take(SIZE as usize / 2 - 1))).is_none());
	}

	#[test]
	fn compute_root_works() {
		assert!(compute_root::<Header, Blake2Hasher, _>(SIZE, 42, vec![Some(1.into()); SIZE as usize]).is_some());
	}

	#[test]
	fn build_proof_fails_when_querying_wrong_block() {
		assert!(build_proof::<Header, Blake2Hasher, _>(
			SIZE, 0, (SIZE * 1000) as u64, vec![Some(1.into()); SIZE as usize]).is_none());
	}

	#[test]
	fn build_proof_works() {
		assert!(build_proof::<Header, Blake2Hasher, _>(
			SIZE, 0, (SIZE / 2) as u64, vec![Some(1.into()); SIZE as usize]).is_some());
	}
}
