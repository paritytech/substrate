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

#[cfg_attr(any(feature = "std", test), macro_use)]
extern crate substrate_runtime_std as rstd;

#[macro_use]
extern crate substrate_runtime_support as runtime_support;

#[cfg(feature = "std")]
extern crate serde;

extern crate substrate_runtime_io as runtime_io;
extern crate substrate_codec as codec;
extern crate substrate_runtime_primitives as primitives;
extern crate safe_mix;

use rstd::prelude::*;
use runtime_io::Hashing;
use primitives::traits::{self, CheckEqual, SimpleArithmetic, SimpleBitOps, Zero, One, Bounded};
use runtime_support::{StorageValue, StorageMap, Parameter};
use safe_mix::TripletMix;

#[cfg(any(feature = "std", test))]
use rstd::marker::PhantomData;
#[cfg(any(feature = "std", test))]
use codec::Slicable;

#[cfg(any(feature = "std", test))]
use runtime_io::{twox_128, TestExternalities};

pub trait Trait {
	type Index: Parameter + Default + SimpleArithmetic + Copy;
	type BlockNumber: Parameter + SimpleArithmetic + Default + Bounded + Copy;
	type Hash: Parameter + SimpleBitOps + Default + Copy + CheckEqual;
	type Hashing: Hashing<Output = Self::Hash>;
	type Digest: Parameter + Default + traits::Digest;
	type AccountId: Parameter + Ord + Default;
	type Header: traits::Header<Number = Self::BlockNumber, Hash = Self::Hash, Digest = Self::Digest>;
}

decl_module! {
	pub struct Module<T: Trait>;
}

decl_storage! {
	trait Store for Module<T: Trait>;

	pub AccountIndex get(account_index): b"sys:non" => default map [ T::AccountId => T::Index ];
	pub BlockHash get(block_hash): b"sys:old" => required map [ T::BlockNumber => T::Hash ];

	pub ExtrinsicIndex get(extrinsic_index): b"sys:xti" => required u32;
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
		<ExtrinsicIndex<T>>::put(0);
	}

	/// Remove temporary "environment" entries in storage.
	pub fn finalise() -> T::Header {
		<RandomSeed<T>>::kill();
		<ExtrinsicIndex<T>>::kill();

		let number = <Number<T>>::take();
		let parent_hash = <ParentHash<T>>::take();
		let digest = <Digest<T>>::take();
		let extrinsics_root = <ExtrinsicsRoot<T>>::take();
		let storage_root = T::Hashing::storage_root();
		<T::Header as traits::Header>::new(number, extrinsics_root, storage_root, parent_hash, digest)
	}

	/// Deposits a log and ensures it matches the blocks log data.
	pub fn deposit_log(item: <T::Digest as traits::Digest>::Item) {
		let mut l = <Digest<T>>::get();
		traits::Digest::push(&mut l, item);
		<Digest<T>>::put(l);
	}

	/// Records a particular block number and hash combination.
	pub fn record_block_hash<H: traits::Header<Number = T::BlockNumber>>(header: &H) {
		// store the header hash in storage; we can't do it before otherwise there would be a
		// cyclic dependency.
		<BlockHash<T>>::insert(header.number(), &T::Hashing::hash_of(header));
	}

	/// Initializes the state following the determination of the genesis block.
	pub fn initialise_genesis_state<H: traits::Header<Number = T::BlockNumber>>(header: &H) {
		Self::record_block_hash(header);
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

	/// Set the parent hash number to something in particular. Can be used as an alternative to
	/// `initialise` for tests that don't need to bother with the other environment entries.
	#[cfg(any(feature = "std", test))]
	pub fn set_parent_hash(n: T::Hash) {
		<ParentHash<T>>::put(n);
	}

	/// Set the random seed to something in particular. Can be used as an alternative to
	/// `initialise` for tests that don't need to bother with the other environment entries.
	#[cfg(any(feature = "std", test))]
	pub fn set_random_seed(n: T::Hash) {
		<RandomSeed<T>>::put(n);
	}

	/// Increment a particular account's nonce by 1.
	pub fn inc_account_index(who: &T::AccountId) {
		<AccountIndex<T>>::insert(who, Self::account_index(who) + T::Index::one());
	}
}

#[cfg(any(feature = "std", test))]
pub struct GenesisConfig<T: Trait>(PhantomData<T>);

#[cfg(any(feature = "std", test))]
impl<T: Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		GenesisConfig(PhantomData)
	}
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> primitives::BuildExternalities for GenesisConfig<T>
{
	fn build_externalities(self) -> runtime_io::TestExternalities {
		use runtime_io::twox_128;
		use codec::Slicable;

		map![
			twox_128(&<BlockHash<T>>::key_for(T::BlockNumber::zero())).to_vec() => [69u8; 32].encode(),
			twox_128(<Number<T>>::key()).to_vec() => 1u64.encode(),
			twox_128(<ParentHash<T>>::key()).to_vec() => [69u8; 32].encode(),
			twox_128(<RandomSeed<T>>::key()).to_vec() => [0u8; 32].encode(),
			twox_128(<ExtrinsicIndex<T>>::key()).to_vec() => [0u8; 4].encode()
		]
	}
}
