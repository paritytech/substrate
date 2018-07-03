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

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

extern crate substrate_runtime_io as runtime_io;
extern crate substrate_codec as codec;
extern crate substrate_runtime_primitives as primitives;
extern crate safe_mix;

use rstd::prelude::*;
use primitives::traits::{self, CheckEqual, SimpleArithmetic, SimpleBitOps, Zero, One, Bounded,
	Hashing, Member, MaybeDisplay};
use runtime_support::{StorageValue, StorageMap, Parameter};
use safe_mix::TripletMix;

#[cfg(any(feature = "std", test))]
use rstd::marker::PhantomData;
#[cfg(any(feature = "std", test))]
use codec::Slicable;

#[cfg(any(feature = "std", test))]
use runtime_io::{twox_128, TestExternalities};

/// Compute the extrinsics root of a list of extrinsics.
pub fn extrinsics_root<H: Hashing, E: codec::Slicable>(extrinsics: &[E]) -> H::Output {
	extrinsics_data_root::<H>(extrinsics.iter().map(codec::Slicable::encode).collect())
}

/// Compute the extrinsics root of a list of extrinsics.
pub fn extrinsics_data_root<H: Hashing>(xts: Vec<Vec<u8>>) -> H::Output {
	let xts = xts.iter().map(Vec::as_slice).collect::<Vec<_>>();
	H::enumerated_trie_root(&xts)
}

pub trait Trait: Eq + Clone {
	type Index: Parameter + Member + Default + MaybeDisplay + SimpleArithmetic + Copy;
	type BlockNumber: Parameter + Member + MaybeDisplay + SimpleArithmetic + Default + Bounded + Copy + rstd::hash::Hash;
	type Hash: Parameter + Member + MaybeDisplay + SimpleBitOps + Default + Copy + CheckEqual + rstd::hash::Hash + AsRef<[u8]>;
	type Hashing: Hashing<Output = Self::Hash>;
	type Digest: Parameter + Member + Default + traits::Digest;
	type AccountId: Parameter + Member + MaybeDisplay + Ord + Default;
	type Header: Parameter + traits::Header<
		Number = Self::BlockNumber,
		Hashing = Self::Hashing,
		Hash = Self::Hash,
		Digest = Self::Digest
	>;
}

decl_module! {
	pub struct Module<T: Trait>;
}

decl_storage! {
	trait Store for Module<T: Trait>;

	pub AccountNonce get(account_nonce): b"sys:non" => default map [ T::AccountId => T::Index ];
	pub BlockHash get(block_hash): b"sys:old" => required map [ T::BlockNumber => T::Hash ];

	pub ExtrinsicIndex get(extrinsic_index): b"sys:xti" => required u32;
	pub ExtrinsicData get(extrinsic_data): b"sys:xtd" => required map [ u32 => Vec<u8> ];
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
		<BlockHash<T>>::insert(*number - One::one(), parent_hash);
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

	/// Calculate the current block's random seed.
	fn calculate_random() -> T::Hash {
		assert!(Self::block_number() > Zero::zero(), "Block number may never be zero");
		(0..81)
			.scan(
				Self::block_number() - One::one(),
				|c, _| { if *c > Zero::zero() { *c -= One::one() }; Some(*c)
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
	pub fn set_random_seed(seed: T::Hash) {
		<RandomSeed<T>>::put(seed);
	}

	/// Increment a particular account's nonce by 1.
	pub fn inc_account_nonce(who: &T::AccountId) {
		<AccountNonce<T>>::insert(who, Self::account_nonce(who) + T::Index::one());
	}

	/// Note what the extrinsic data of the current extrinsic index is. If this is called, then
	/// ensure `derive_extrinsics` is also called before block-building is completed.
	pub fn note_extrinsic(encoded_xt: Vec<u8>) {
		<ExtrinsicData<T>>::insert(Self::extrinsic_index(), encoded_xt);
	}

	/// Remove all extrinsics data and save the extrinsics trie root.
	pub fn derive_extrinsics() {
		let extrinsics = (0..Self::extrinsic_index()).map(<ExtrinsicData<T>>::take).collect();
		let xts_root = extrinsics_data_root::<T::Hashing>(extrinsics);
		<ExtrinsicsRoot<T>>::put(xts_root);
	}
}

#[cfg(any(feature = "std", test))]
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct GenesisConfig<T: Trait>(PhantomData<T>);

#[cfg(any(feature = "std", test))]
impl<T: Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		GenesisConfig(PhantomData)
	}
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> primitives::BuildStorage for GenesisConfig<T>
{
	fn build_storage(self) -> Result<runtime_io::TestExternalities, String> {
		use runtime_io::twox_128;
		use codec::Slicable;

		Ok(map![
			twox_128(&<BlockHash<T>>::key_for(T::BlockNumber::zero())).to_vec() => [69u8; 32].encode(),
			twox_128(<Number<T>>::key()).to_vec() => 1u64.encode(),
			twox_128(<ParentHash<T>>::key()).to_vec() => [69u8; 32].encode(),
			twox_128(<RandomSeed<T>>::key()).to_vec() => [0u8; 32].encode(),
			twox_128(<ExtrinsicIndex<T>>::key()).to_vec() => [0u8; 4].encode()
		])
	}
}
