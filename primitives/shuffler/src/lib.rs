#![cfg_attr(not(feature = "std"), no_std)]
use sp_api::{Encode, HashT};

use sp_runtime::traits::BlakeTwo256;

use sp_std::{collections::btree_map::BTreeMap, convert::TryInto};

use sp_core::H256;
use sp_std::{collections::vec_deque::VecDeque, vec::Vec};

#[cfg(feature = "std")]
use sp_api::{ApiExt, ApiRef, ProvideRuntimeApi, TransactionOutcome};
#[cfg(feature = "std")]
use sp_core::crypto::Ss58Codec;
#[cfg(feature = "std")]
use sp_runtime::{generic::BlockId, traits::Block as BlockT, AccountId32};
#[cfg(feature = "std")]
use ver_api::VerApi;

pub struct Xoshiro256PlusPlus {
	s: [u64; 4],
}

fn rotl(x: u64, k: u64) -> u64 {
	((x) << (k)) | ((x) >> (64 - (k)))
}

impl Xoshiro256PlusPlus {
	#[inline]
	fn from_seed(seed: [u8; 32]) -> Xoshiro256PlusPlus {
		Xoshiro256PlusPlus {
			s: [
				u64::from_le_bytes(seed[0..8].try_into().unwrap()),
				u64::from_le_bytes(seed[8..16].try_into().unwrap()),
				u64::from_le_bytes(seed[16..24].try_into().unwrap()),
				u64::from_le_bytes(seed[24..32].try_into().unwrap()),
			],
		}
	}

	fn next_u32(&mut self) -> u32 {
		let t: u64 = self.s[1] << 17;

		self.s[2] ^= self.s[0];
		self.s[3] ^= self.s[1];
		self.s[1] ^= self.s[2];
		self.s[0] ^= self.s[3];

		self.s[2] ^= t;

		self.s[3] = rotl(self.s[3], 45);

		(self.s[0].wrapping_add(self.s[3])) as u32
	}

	fn next_u64(&mut self) -> u64 {
		let first = ((self.next_u32()) as u64) << 32;
		let second = self.next_u32() as u64;
		return first | second;
	}
}

/// In order to be able to recreate shuffling order anywere lets use
/// explicit algorithms
/// - Xoshiro256StarStar as random number generator
/// - Fisher-Yates variation as shuffling algorithm
///
/// ref https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle
///
/// To shuffle an array a of n elements (indices 0..n-1):
///
/// for i from n−1 downto 1 do
///     j ← random integer such that 0 ≤ j ≤ i
///     exchange a[j] and a[i]
struct FisherYates(Xoshiro256PlusPlus);

impl FisherYates {
	fn from_bytes(bytes: [u8; 32]) -> Self {
		Self(Xoshiro256PlusPlus::from_seed(bytes))
	}

	fn shuffle<T>(&mut self, data: &mut [T]) {
		for i in (1..(data.len())).rev() {
			// vec length may be up to 64 bytes so we should use
			// big enought number
			let random = self.0.next_u64();
			let j = random % ((i + 1) as u64);
			data.swap(i, j as usize);
		}
	}
}

pub fn shuffle_using_seed<A: sp_std::cmp::Ord + Encode + Clone, E: Encode + Clone>(
	extrinsics: Vec<(Option<A>, E)>,
	seed: &H256,
) -> Vec<E> {
	log::debug!(target: "block_shuffler", "shuffling extrinsics with seed: {:2X?}", seed.as_bytes());
	log::debug!(target: "block_shuffler", "origin order: [");
	for (_, tx) in extrinsics.iter() {
		log::debug!(target: "block_shuffler", "{:?}", BlakeTwo256::hash_of(tx));
	}
	log::debug!(target: "block_shuffler", "]");

	let mut fy = FisherYates::from_bytes(seed.to_fixed_bytes());

	// generate exact number of slots for each account
	// [ Alice, Alice, Alice, ... , Bob, Bob, Bob, ... ]
	// let mut slots: Vec<Option<_>> =
	// 	extrinsics.iter().map(|(who, _)| who).cloned().collect();
	// let mut slots = Vec::with_capacity(extrinsics.len());

	// initial slots - just inherents
	let mut slots = extrinsics
		.iter()
		.filter(|tx| tx.0.is_none())
		.map(|(_, tx)| tx)
		.cloned()
		.collect::<Vec<_>>();
	let only_extrinsics =
		extrinsics.into_iter().filter(|tx| tx.0.is_some()).collect::<Vec<(_, _)>>();

	let mut grouped_extrinsics: BTreeMap<Option<_>, VecDeque<_>> =
		only_extrinsics.into_iter().fold(BTreeMap::new(), |mut groups, (who, tx)| {
			groups.entry(who).or_insert_with(VecDeque::new).push_back(tx);
			groups
		});

	// let mut txs_per_user = grouped_extrinsics.iter().map(|(who,txs)|
	// (who,txs.size())).collect::<BTreeMap<_>>();
	while !grouped_extrinsics.is_empty() {
		let keys = grouped_extrinsics.keys().cloned().collect::<Vec<_>>();
		let from = slots.len();
		for k in keys {
			// TODO remove
			let txs_from_account = grouped_extrinsics.get_mut(&k).unwrap();
			slots.push(txs_from_account.pop_front().unwrap());
			if txs_from_account.is_empty() {
				grouped_extrinsics.remove(&k);
			}
		}
		let to = slots.len();
		fy.shuffle(&mut slots[from..to]);
	}

	// fill slots using extrinsics in order
	// [ Alice, Bob, ... , Alice, Bob ]
	//              ↓↓↓
	// [ AliceExtrinsic1, BobExtrinsic1, ... , AliceExtrinsicN, BobExtrinsicN ]
	// let shuffled_extrinsics: Vec<_> = slots
	// 	.into_iter()
	// 	.map(|who| grouped_extrinsics.get_mut(&who).unwrap().pop_front().unwrap())
	// 	.collect();

	log::debug!(target: "block_shuffler", "shuffled order:[");
	for tx in slots.iter() {
		let tx_hash = BlakeTwo256::hash(&tx.encode());
		log::debug!(target: "block_shuffler", "{:?}", tx_hash);
	}
	log::debug!(target: "block_shuffler", "]");

	slots
}

/// shuffles extrinsics assuring that extrinsics signed by single account will be still evaluated
/// in proper order
#[cfg(feature = "std")]
pub fn shuffle<'a, Block, Api>(
	api: &ApiRef<'a, Api::Api>,
	block_id: &BlockId<Block>,
	extrinsics: Vec<Block::Extrinsic>,
	seed: &H256,
) -> Vec<Block::Extrinsic>
where
	Block: BlockT,
	Api: ProvideRuntimeApi<Block> + 'a,
	Api::Api: VerApi<Block>,
{
	if extrinsics.len() <= 1 {
		return extrinsics;
	}
	let extrinsics: Vec<(Option<AccountId32>, Block::Extrinsic)> = extrinsics
		.into_iter()
		.map(|tx| {
			let tx_hash = BlakeTwo256::hash(&tx.encode());
			let who = api.execute_in_transaction(|api| {
				// store deserialized data and revert state modification caused by 'get_info' call
				match api.get_signer(block_id, tx.clone()){
					Ok(result) => TransactionOutcome::Rollback(result),
					Err(_) => TransactionOutcome::Rollback(None)
				}
			});
			log::debug!(target: "block_shuffler", "who:{:48}  extrinsic:{:?}",who.clone().map(|x| x.0.to_ss58check()).unwrap_or_else(|| String::from("None")), tx_hash);
			(who.map(|x| x.0), tx)
		}).collect();

	shuffle_using_seed(extrinsics, seed)
}

#[derive(derive_more::Display, Debug)]
pub enum Error {
	#[display(fmt = "Cannot apply inherents")]
	InherentApplyError,
	#[display(fmt = "Cannot read seed from the runtime api ")]
	SeedFetchingError,
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::{
		collections::{BTreeSet, HashMap},
		str::FromStr,
	};

	#[test]
	fn shuffle_using_seed_works() {
		let alice = String::from("Alice");
		let bob = String::from("Bob");
		let charlie = String::from("Charlie");
		let mut txs = BTreeMap::new();
		txs.insert(alice.clone(), (1..9).into_iter().collect::<BTreeSet<_>>());
		txs.insert(bob.clone(), (10..16).into_iter().collect::<BTreeSet<_>>());
		txs.insert(charlie.clone(), (20..23).into_iter().collect::<BTreeSet<_>>());

		let txs_with_author = txs
			.iter()
			.map(|(who, txs)| std::iter::repeat(Some(who)).zip(txs))
			.flatten()
			.collect::<Vec<_>>();
		let origin_order = txs_with_author.iter().map(|(_, tx)| tx).cloned().collect::<Vec<_>>();

		let shuffled_txs = shuffle_using_seed(txs_with_author.clone(), &Default::default());

		assert_ne!(origin_order, shuffled_txs);
		assert_eq!(origin_order.len(), shuffled_txs.len());

		// one tx from tree account
		assert_eq!(
			(&shuffled_txs[0..3]).iter().collect::<BTreeSet<_>>(),
			[&1, &10, &20].iter().collect::<BTreeSet<_>>()
		);
		assert_eq!(
			(&shuffled_txs[3..6]).iter().collect::<BTreeSet<_>>(),
			[&2, &11, &21].iter().collect::<BTreeSet<_>>()
		);
		assert_eq!(
			(&shuffled_txs[6..9]).iter().collect::<BTreeSet<_>>(),
			[&3, &12, &22].iter().collect::<BTreeSet<_>>()
		);

		// one tx from two account
		assert_eq!(
			(&shuffled_txs[9..11]).iter().collect::<BTreeSet<_>>(),
			[&4, &13].iter().collect::<BTreeSet<_>>()
		);
		assert_eq!(
			(&shuffled_txs[11..13]).iter().collect::<BTreeSet<_>>(),
			[&5, &14].iter().collect::<BTreeSet<_>>()
		);
		assert_eq!(
			(&shuffled_txs[13..15]).iter().collect::<BTreeSet<_>>(),
			[&6, &15].iter().collect::<BTreeSet<_>>()
		);

		// tx from remaining account
		assert_eq!(
			(&shuffled_txs[15..]).iter().collect::<BTreeSet<_>>(),
			[&7, &8].iter().collect::<BTreeSet<_>>()
		);
	}

	#[test]
	fn shuffle_using_different_seed_produces_different_results() {
		let input = vec![
			(Some("A"), 1),
			(Some("A"), 2),
			(Some("A"), 3),
			(Some("A"), 4),
			(Some("A"), 5),
			(Some("B"), 11),
			(Some("B"), 12),
			(Some("C"), 21),
		];

		let shuffled1 = shuffle_using_seed(
			input.clone(),
			&H256::from_str("0xff8611a4d212fc161dae19dd57f0f1ba9309f45d6207da13f2d3eab4c6839e91")
				.unwrap(),
		);
		let shuffled2 = shuffle_using_seed(
			input.clone(),
			&H256::from_str("0x0876d51dc2c109b2e9bca322e8706879d68984a8031a537d76d0b21693a3dbd0")
				.unwrap(),
		);
		assert_ne!(shuffled1, shuffled2);
	}

	#[test]
	fn inherents_executed_with_highest_priority() {
		let input = vec![
			(None, 1),
			(None, 2),
			(None, 3),
			(None, 4),
			(None, 5),
			(Some("A"), 10),
			(Some("B"), 20),
			(Some("C"), 30),
			(Some("D"), 40),
		];

		let shuffled = shuffle_using_seed(
			input.clone(),
			&H256::from_str("0xff8611a4d212fc161dae19dd57f0f1ba9309f45d6207da13f2d3eab4c6839e91")
				.unwrap(),
		);

		// check that txs comming from None account are in the front
		assert_eq!(shuffled[0], 1);
		assert_eq!(shuffled[1], 2);
		assert_eq!(shuffled[2], 3);
		assert_eq!(shuffled[3], 4);
		assert_eq!(shuffled[4], 5);

		// check that rest of the transactions is still shuffled
		let origin_order = input.iter().map(|(_, tx)| tx).cloned().collect::<Vec<_>>();
		assert_ne!(origin_order, shuffled);
	}

	#[test]
	fn check_shuffling_works_for_two_elements() {
		let mut fy = FisherYates::from_bytes([
			1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5,
			6, 7, 8,
		]);

		let mut set = HashMap::new();
		let count = 100000;

		for _ in 1..count {
			let mut input = [1, 2];
			fy.shuffle(&mut input[..]);
			*set.entry(input).or_insert(1) += 1;
		}

		let first_variant = *set.get(&[1, 2]).unwrap() as f64 / count as f64;
		let second_variant = *set.get(&[2, 1]).unwrap() as f64 / count as f64;

		assert_eq!(set.len(), 2);
		assert!(first_variant >= 0.499);
		assert!(second_variant >= 0.499);
	}

	#[test]
	fn check_shuffling_works_for_three_elements() {
		let mut fy = FisherYates::from_bytes([
			1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5,
			6, 7, 8,
		]);

		let mut set = HashMap::new();
		let count = 100000;

		for _ in 1..count {
			let mut input = [1, 2, 3];
			fy.shuffle(&mut input[..]);
			*set.entry(input).or_insert(1) += 1;
		}

		assert_eq!(set.len(), 3 * 2 * 1);

		for (_, number_of_occurances) in set {
			let expected_number_of_occurances = count as f64 / (3 * 2 * 1) as f64 * 0.98;
			assert!(number_of_occurances as f64 >= expected_number_of_occurances);
		}
	}
}
