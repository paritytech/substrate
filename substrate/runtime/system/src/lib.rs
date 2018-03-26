// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! System manager: Handles lowest level stuff like depositing logs, basic set up and take down of
//! temporary storage entries, access to old block hashes.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg_attr(any(feature = "std", test), macro_use)] extern crate substrate_runtime_std as rstd;
#[macro_use] extern crate substrate_runtime_support as runtime_support;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_codec as codec;
extern crate substrate_runtime_primitives as primitives;

#[cfg(feature = "std")] extern crate serde;

extern crate safe_mix;

use rstd::prelude::*;
use primitives::{Digesty, CheckEqual, SimpleArithmetic, SimpleBitOps, Zero, One, Bounded, Hashing, Headery};
use runtime_support::{StorageValue, StorageMap, Parameter};
use safe_mix::TripletMix;

#[cfg(any(feature = "std", test))]
use runtime_io::{twox_128, TestExternalities};

pub trait Trait {
	type Index: Parameter + Default + SimpleArithmetic + Copy;
	type BlockNumber: Parameter + SimpleArithmetic + Default + Bounded + Copy;
	type Hash: Parameter + SimpleBitOps + Default + Copy + CheckEqual;
	type Hashing: Hashing<Output = Self::Hash>;
	type Digest: Parameter + Default + Digesty;
	type AccountId: Parameter + Ord;
	type Header: Headery<Number = Self::BlockNumber, Hash = Self::Hash, Digest = Self::Digest>;
}

decl_module! {
	pub struct Module<T: Trait>;
}

decl_storage! {
	trait Store for Module<T: Trait>;

	pub AccountIndex get(account_index): b"sys:non" => default map [ T::AccountId => T::Index ];
	pub BlockHash get(block_hash): b"sys:old" => required map [ T::BlockNumber => T::Hash ];

	RandomSeed get(random_seed): b"sys:rnd" => required T::Hash;
	// The current block number being processed. Set by `execute_block`.
	Number get(block_number): b"sys:num" => required T::BlockNumber;
	ParentHash get(parent_hash): b"sys:pha" => required T::Hash;
	ExtrinsicsRoot get(extrinsics_root): b"sys:txr" => required T::Hash;
	Digest get(digest): b"sys:dig" => default T::Digest;
}

impl<T: Trait> Module<T> {
	/// Start the execution of a particular block.
	pub fn initialise(number: &T::BlockNumber, parent_hash: &T::Hash, txs_root: &T::Hash) {
		// populate environment.
		<Number<T>>::put(number);
		<ParentHash<T>>::put(parent_hash);
		<ExtrinsicsRoot<T>>::put(txs_root);
		<RandomSeed<T>>::put(Self::calculate_random());
	}

	/// Remove temporary "environment" entries in storage.
	pub fn finalise() -> T::Header {
		<RandomSeed<T>>::kill();

		let number = <Number<T>>::take();
		let parent_hash = <ParentHash<T>>::take();
		let digest = <Digest<T>>::take();
		let extrinsics_root = <ExtrinsicsRoot<T>>::take();
		let storage_root = T::Hashing::storage_root();
		T::Header::new(number, extrinsics_root, storage_root, parent_hash, digest)
	}

	/// Deposits a log and ensures it matches the blocks log data.
	pub fn deposit_log(item: <T::Digest as Digesty>::Item) {
		let mut l = <Digest<T>>::get();
		l.push(item);
		<Digest<T>>::put(l);
	}

	/// Records a particular block number and hash combination.
	pub fn record_block_hash<H: Headery<Number = T::BlockNumber>>(header: &H) {
		// store the header hash in storage; we can't do it before otherwise there would be a
		// cyclic dependency.
		<BlockHash<T>>::insert(header.number(), &T::Hashing::hash_of(header));
	}

	/// Calculate the current block's random seed.
	fn calculate_random() -> T::Hash {
		(0..81)
			.scan(
				{ let mut n = Self::block_number().clone(); n -= T::BlockNumber::one(); n },
				|c, _| { if *c > T::BlockNumber::zero() { *c -= T::BlockNumber::one() }; Some(c.clone())
			})
			.map(Self::block_hash)
			.triplet_mix()
	}

	/// Get the basic externalities for this module, useful for tests.
	#[cfg(any(feature = "std", test))]
	pub fn externalities() -> TestExternalities {
		map![
			twox_128(&<BlockHash<T>>::key_for(T::BlockNumber::zero())).to_vec() => [69u8; 32].encode(),	// TODO: replace with Hash::default().encode
			twox_128(<Number<T>>::key()).to_vec() => T::BlockNumber::one().encode(),
			twox_128(<ParentHash<T>>::key()).to_vec() => [69u8; 32].encode(),	// TODO: replace with Hash::default().encode
			twox_128(<RandomSeed<T>>::key()).to_vec() => T::Hash::default().encode()
		]
	}

	/// Set the block number to something in particular. Can be used as an alternative to
	/// `initialise` for tests that don't need to bother with the other environment entries.
	#[cfg(any(feature = "std", test))]
	pub fn set_block_number(n: T::BlockNumber) {
		<Number<T>>::put(n);
	}

	/// Increment a particular account's nonce by 1.
	pub fn inc_account_index(who: &T::AccountId) {
		<AccountIndex<T>>::insert(who, Self::account_index(who) + T::Index::one());
	}
}

#[cfg(test)]
mod tests {
/*
	use super::*;
	#[test]
	fn staking_balance_transfer_dispatch_works() {
		let mut t: TestExternalities = map![
			twox_128(&staking::FreeBalanceOf::key_for(*One)).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(staking::TransactionFee::key()).to_vec() => vec![10u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(&BlockHash::key_for(&0)).to_vec() => [69u8; 32].encode()
		];

		let tx = UncheckedTransaction {
			transaction: Transaction {
				signed: One.into(),
				nonce: 0,
				function: PubCall::Staking(StakingCall::transfer(Two.into(), 69)),
			},
			signature: hex!("3a682213cb10e8e375fe0817fe4d220a4622d910088809ed7fc8b4ea3871531dbadb22acfedd28a100a0b7bd2d274e0ff873655b13c88f4640b5569db3222706").into(),
		};

		with_externalities(&mut t, || {
			internal::initialise_block(&Header::from_block_number(1));
			internal::execute_transaction(tx);
			assert_eq!(staking::balance(&One), 32);
			assert_eq!(staking::balance(&Two), 69);
		});
	}

	fn new_test_ext() -> TestExternalities {
		staking::testing::externalities(2, 2, 0)
	}

	#[test]
	fn block_import_works() {
		let mut t = new_test_ext();

		let h = Header {
			parent_hash: [69u8; 32].into(),
			number: 1,
			state_root: hex!("cc3f1f5db826013193e502c76992b5e933b12367e37a269a9822b89218323e9f").into(),
			extrinsics_root: hex!("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421").into(),
			digest: Digest { logs: vec![], },
		};

		let b = Block {
			header: h,
			transactions: vec![],
		};

		with_externalities(&mut t, || {
			execute_block(b);
		});
	}

	#[test]
	#[should_panic]
	fn block_import_of_bad_state_root_fails() {
		let mut t = new_test_ext();

		let h = Header {
			parent_hash: [69u8; 32].into(),
			number: 1,
			state_root: [0u8; 32].into(),
			extrinsics_root: hex!("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421").into(),
			digest: Digest { logs: vec![], },
		};

		let b = Block {
			header: h,
			transactions: vec![],
		};

		with_externalities(&mut t, || {
			execute_block(b);
		});
	}

	#[test]
	#[should_panic]
	fn block_import_of_bad_extrinsics_root_fails() {
		let mut t = new_test_ext();

		let h = Header {
			parent_hash: [69u8; 32].into(),
			number: 1,
			state_root: hex!("1ab2dbb7d4868a670b181327b0b6a58dc64b10cfb9876f737a5aa014b8da31e0").into(),
			extrinsics_root: [0u8; 32].into(),
			digest: Digest { logs: vec![], },
		};

		let b = Block {
			header: h,
			transactions: vec![],
		};

		with_externalities(&mut t, || {
			execute_block(b);
		});
	}
	*/
}
