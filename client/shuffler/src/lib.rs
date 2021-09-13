#![cfg_attr(not(feature = "std"), no_std)]
use sp_api::Encode;
use sp_api::HashT;

use sp_runtime::traits::{BlakeTwo256, Block as BlockT};
use sp_runtime::AccountId32;
use sp_std::collections::btree_map::BTreeMap;
use sp_std::convert::TryInto;

use sp_std::collections::vec_deque::VecDeque;
use sp_std::vec::Vec;
use sp_core::H256;

#[cfg(feature = "std")]
use extrinsic_info_runtime_api::runtime_api::ExtrinsicInfoRuntimeApi;
#[cfg(feature = "std")]
use sp_api::{ApiExt, ApiRef, ProvideRuntimeApi, TransactionOutcome};
#[cfg(feature = "std")]
use sp_core::crypto::Ss58Codec;
#[cfg(feature = "std")]
use sp_runtime::generic::BlockId;

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
///
fn fisher_yates<T>(data: &mut Vec<T>, seed: [u8; 32]) {
	let mut s = Xoshiro256PlusPlus::from_seed(seed);
	for i in (1..(data.len())).rev() {
		let j = s.next_u32() % (i as u32);
		data.swap(i, j as usize);
	}
}

pub fn shuffle_using_seed<E: Encode>(
	extrinsics: Vec<(Option<AccountId32>, E)>,
	seed: &H256,
) -> Vec<E> {
	log::debug!(target: "block_shuffler", "shuffling extrinsics with seed: {:2X?}", seed.as_bytes());
	log::debug!(target: "block_shuffler", "origin order: [");
	for (_,tx) in extrinsics.iter() {
		log::debug!(target: "block_shuffler", "{:?}", BlakeTwo256::hash(&tx.encode()));
	}
	log::debug!(target: "block_shuffler", "]");

	// generate exact number of slots for each account
	// [ Alice, Alice, Alice, ... , Bob, Bob, Bob, ... ]
	let mut slots: Vec<Option<AccountId32>> =
		extrinsics.iter().map(|(who, _)| who).cloned().collect();

	let mut grouped_extrinsics: BTreeMap<Option<AccountId32>, VecDeque<_>> = extrinsics
		.into_iter()
		.fold(BTreeMap::new(), |mut groups, (who, tx)| {
			groups
				.entry(who)
				.or_insert_with(VecDeque::new)
				.push_back(tx);
			groups
		});

	// shuffle slots
	fisher_yates(&mut slots, seed.to_fixed_bytes());

	// fill slots using extrinsics in order
	// [ Alice, Bob, ... , Alice, Bob ]
	//              ↓↓↓
	// [ AliceExtrinsic1, BobExtrinsic1, ... , AliceExtrinsicN, BobExtrinsicN ]
	let shuffled_extrinsics: Vec<_> = slots
		.into_iter()
		.map(|who| {
			grouped_extrinsics
				.get_mut(&who)
				.unwrap()
				.pop_front()
				.unwrap()
		})
	.collect();

	log::debug!(target: "block_shuffler", "shuffled order:[");
	for tx in shuffled_extrinsics.iter() {
		let tx_hash = BlakeTwo256::hash(&tx.encode());
		log::debug!(target: "block_shuffler", "{:?}", tx_hash);
	}
	log::debug!(target: "block_shuffler", "]");

	shuffled_extrinsics
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
	Api::Api: ExtrinsicInfoRuntimeApi<Block>,
{

	let extrinsics: Vec<(Option<AccountId32>, Block::Extrinsic)> = extrinsics
		.into_iter()
		.map(|tx| {
			let tx_hash = BlakeTwo256::hash(&tx.encode());
			let who = api.execute_in_transaction(|api| {
				// store deserialized data and revert state modification caused by 'get_info' call
				match api.get_info(block_id, tx.clone()){
					Ok(result) => TransactionOutcome::Rollback(result),
					Err(_) => TransactionOutcome::Rollback(None)
				}
			})
			.map(|info| Some(info.who)).unwrap_or(None);
			log::debug!(target: "block_shuffler", "who:{:48}  extrinsic:{:?}",who.clone().map(|x| x.to_ss58check()).unwrap_or_else(|| String::from("None")), tx_hash);
			(who, tx)
		}).collect();

	shuffle_using_seed::<Block::Extrinsic>(extrinsics, seed)
}

#[derive(derive_more::Display, Debug)]
pub enum Error {
	#[display(fmt = "Cannot apply inherents")]
	InherentApplyError,
	#[display(fmt = "Cannot read seed from the runtime api ")]
	SeedFetchingError,
}
