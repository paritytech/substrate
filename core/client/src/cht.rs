// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

use std::collections::HashSet;

use hash_db;
use trie;

use primitives::{H256, convert_hash};
use runtime_primitives::traits::{As, Header as HeaderT, SimpleArithmetic, One};
use state_machine::backend::InMemory as InMemoryState;
use state_machine::{MemoryDB, TrieBackend, Backend as StateBackend,
	prove_read_on_trie_backend, read_proof_check, read_proof_check_on_proving_backend};

use crate::error::{Error as ClientError, Result as ClientResult};

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
) -> ClientResult<Hasher::Out>
	where
		Header: HeaderT,
		Hasher: hash_db::Hasher,
		Hasher::Out: Ord,
		I: IntoIterator<Item=ClientResult<Option<Header::Hash>>>,
{
	Ok(trie::trie_root::<Hasher, _, _, _>(
		build_pairs::<Header, I>(cht_size, cht_num, hashes)?
	))
}

/// Build CHT-based header proof.
pub fn build_proof<Header, Hasher, BlocksI, HashesI>(
	cht_size: u64,
	cht_num: Header::Number,
	blocks: BlocksI,
	hashes: HashesI
) -> ClientResult<Vec<Vec<u8>>>
	where
		Header: HeaderT,
		Hasher: hash_db::Hasher,
		Hasher::Out: Ord,
		BlocksI: IntoIterator<Item=Header::Number>,
		HashesI: IntoIterator<Item=ClientResult<Option<Header::Hash>>>,
{
	let transaction = build_pairs::<Header, _>(cht_size, cht_num, hashes)?
		.into_iter()
		.map(|(k, v)| (None, k, Some(v)))
		.collect::<Vec<_>>();
	let storage = InMemoryState::<Hasher>::default().update(transaction);
	let trie_storage = storage.try_into_trie_backend()
		.expect("InMemoryState::try_into_trie_backend always returns Some; qed");
	let mut total_proof = HashSet::new();
	for block in blocks.into_iter() {
		debug_assert_eq!(block_to_cht_number(cht_size, block), Some(cht_num));

		let (value, proof) = prove_read_on_trie_backend(&trie_storage, &encode_cht_key(block))?;
		assert!(value.is_some(), "we have just built trie that includes the value for block");
		total_proof.extend(proof);
	}
	Ok(total_proof.into_iter().collect())
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
		Hasher: hash_db::Hasher,
		Hasher::Out: Ord,
{
	do_check_proof::<Header, Hasher, _>(local_root, local_number, remote_hash, move |local_root, local_cht_key|
		read_proof_check::<Hasher>(local_root, remote_proof,
			local_cht_key).map_err(|e| ClientError::from(e)))
}

/// Check CHT-based header proof on pre-created proving backend.
pub fn check_proof_on_proving_backend<Header, Hasher>(
	local_root: Header::Hash,
	local_number: Header::Number,
	remote_hash: Header::Hash,
	proving_backend: &TrieBackend<MemoryDB<Hasher>, Hasher>,
) -> ClientResult<()>
	where
		Header: HeaderT,
		Hasher: hash_db::Hasher,
		Hasher::Out: Ord,
{
	do_check_proof::<Header, Hasher, _>(local_root, local_number, remote_hash, |_, local_cht_key|
		read_proof_check_on_proving_backend::<Hasher>(
			proving_backend, local_cht_key).map_err(|e| ClientError::from(e)))
}

/// Check CHT-based header proof using passed checker function.
fn do_check_proof<Header, Hasher, F>(
	local_root: Header::Hash,
	local_number: Header::Number,
	remote_hash: Header::Hash,
	checker: F,
) -> ClientResult<()>
	where
		Header: HeaderT,
		Hasher: hash_db::Hasher,
		Hasher::Out: Ord,
		F: FnOnce(Hasher::Out, &[u8]) -> ClientResult<Option<Vec<u8>>>,
{
	let root: Hasher::Out = convert_hash(&local_root);
	let local_cht_key = encode_cht_key(local_number);
	let local_cht_value = checker(root, &local_cht_key)?;
	let local_cht_value = local_cht_value.ok_or_else(|| ClientError::InvalidCHTProof)?;
	let local_hash = decode_cht_value(&local_cht_value).ok_or_else(|| ClientError::InvalidCHTProof)?;
	match &local_hash[..] == remote_hash.as_ref() {
		true => Ok(()),
		false => Err(ClientError::InvalidCHTProof.into()),
	}

}

/// Group ordered blocks by CHT number and call functor with blocks of each group.
pub fn for_each_cht_group<Header, I, F, P>(
	cht_size: u64,
	blocks: I,
	mut functor: F,
	mut functor_param: P,
) -> ClientResult<()>
	where
		Header: HeaderT,
		I: IntoIterator<Item=Header::Number>,
		F: FnMut(P, Header::Number, Vec<Header::Number>) -> ClientResult<P>,
{
	let mut current_cht_num = None;
	let mut current_cht_blocks = Vec::new();
	for block in blocks {
		let new_cht_num = match block_to_cht_number(cht_size, block.as_()) {
			Some(new_cht_num) => new_cht_num,
			None => return Err(ClientError::Backend(format!(
				"Cannot compute CHT root for the block #{}", block)).into()
			),
		};

		let advance_to_next_cht = current_cht_num.is_some() && current_cht_num != Some(new_cht_num);
		if advance_to_next_cht {
			let current_cht_num = current_cht_num.expect("advance_to_next_cht is true;
				it is true only when current_cht_num is Some; qed");
			assert!(new_cht_num > current_cht_num, "for_each_cht_group only supports ordered iterators");

			functor_param = functor(
				functor_param,
				As::sa(current_cht_num),
				::std::mem::replace(&mut current_cht_blocks, Vec::new()),
			)?;
		}

		current_cht_blocks.push(block);
		current_cht_num = Some(new_cht_num);
	}

	if let Some(current_cht_num) = current_cht_num {
		functor(
			functor_param,
			As::sa(current_cht_num),
			::std::mem::replace(&mut current_cht_blocks, Vec::new()),
		)?;
	}

	Ok(())
}

/// Build pairs for computing CHT.
fn build_pairs<Header, I>(
	cht_size: u64,
	cht_num: Header::Number,
	hashes: I
) -> ClientResult<Vec<(Vec<u8>, Vec<u8>)>>
	where
		Header: HeaderT,
		I: IntoIterator<Item=ClientResult<Option<Header::Hash>>>,
{
	let start_num = start_number(cht_size, cht_num);
	let mut pairs = Vec::new();
	let mut hash_number = start_num;
	for hash in hashes.into_iter().take(cht_size as usize) {
		let hash = hash?.ok_or_else(|| ClientError::from(
			ClientError::MissingHashRequiredForCHT(cht_num.as_(), hash_number.as_())
		))?;
		pairs.push((
			encode_cht_key(hash_number).to_vec(),
			encode_cht_value(hash)
		));
		hash_number += Header::Number::one();
	}

	if pairs.len() as u64 == cht_size {
		Ok(pairs)
	} else {
		Err(ClientError::MissingHashRequiredForCHT(cht_num.as_(), hash_number.as_()))
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
		assert!(build_pairs::<Header, _>(SIZE, 0,
			::std::iter::repeat_with(|| Ok(Some(H256::from_low_u64_be(1)))).take(SIZE as usize / 2)).is_err());
	}

	#[test]
	fn build_pairs_fails_when_missing_block() {
		assert!(build_pairs::<Header, _>(SIZE, 0, ::std::iter::repeat_with(|| Ok(Some(H256::from_low_u64_be(1)))).take(SIZE as usize / 2)
			.chain(::std::iter::once(Ok(None)))
			.chain(::std::iter::repeat_with(|| Ok(Some(H256::from_low_u64_be(2)))).take(SIZE as usize / 2 - 1))).is_err());
	}

	#[test]
	fn compute_root_works() {
		assert!(compute_root::<Header, Blake2Hasher, _>(SIZE, 42,
			::std::iter::repeat_with(|| Ok(Some(H256::from_low_u64_be(1)))).take(SIZE as usize)).is_ok());
	}

	#[test]
	#[should_panic]
	fn build_proof_panics_when_querying_wrong_block() {
		assert!(build_proof::<Header, Blake2Hasher, _, _>(
			SIZE, 0, vec![(SIZE * 1000) as u64],
				::std::iter::repeat_with(|| Ok(Some(H256::from_low_u64_be(1)))).take(SIZE as usize)).is_err());
	}

	#[test]
	fn build_proof_works() {
		assert!(build_proof::<Header, Blake2Hasher, _, _>(
			SIZE, 0, vec![(SIZE / 2) as u64],
				::std::iter::repeat_with(|| Ok(Some(H256::from_low_u64_be(1)))).take(SIZE as usize)).is_ok());
	}

	#[test]
	#[should_panic]
	fn for_each_cht_group_panics() {
		let _ = for_each_cht_group::<Header, _, _, _>(SIZE, vec![SIZE * 5, SIZE * 2], |_, _, _| Ok(()), ());
	}

	#[test]
	fn for_each_cht_group_works() {
		let _ = for_each_cht_group::<Header, _, _, _>(SIZE, vec![
			SIZE * 2 + 1, SIZE * 2 + 2, SIZE * 2 + 5,
			SIZE * 4 + 1, SIZE * 4 + 7,
			SIZE * 6 + 1
		], |_, cht_num, blocks| {
			match cht_num {
				2 => assert_eq!(blocks, vec![SIZE * 2 + 1, SIZE * 2 + 2, SIZE * 2 + 5]),
				4 => assert_eq!(blocks, vec![SIZE * 4 + 1, SIZE * 4 + 7]),
				6 => assert_eq!(blocks, vec![SIZE * 6 + 1]),
				_ => unreachable!(),
			}

			Ok(())
		}, ());
	}
}
