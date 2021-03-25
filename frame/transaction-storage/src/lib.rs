// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Transaction storage pallet. Indexes transactions and manages storage proofs.


// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{
	traits::{ReservableCurrency, Currency},
	dispatch::{Dispatchable, GetDispatchInfo},
};
use sp_std::prelude::*;
use sp_std::{result};
use codec::{Encode, Decode};
use sp_runtime::{
	traits::{
		Saturating, BlakeTwo256, Hash, Zero,
	},
};
use sp_storage_proof::StorageProof;

/// A type alias for the balance type from this pallet's point of view.
type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

// Re-export pallet items so that they can be accessed from the crate namespace.
pub use pallet::*;

const CHUNK_SIZE: usize = sp_storage_proof::CHUNK_SIZE;

#[derive(Encode, Decode, sp_runtime::RuntimeDebug)]
pub struct TransactionInfo {
	chunk_root: <BlakeTwo256 as Hash>::Output,
	content_hash: <BlakeTwo256 as Hash>::Output,
	size: u32,
}

// Definition of the pallet logic, to be aggregated at runtime definition through
// `construct_runtime`.
#[frame_support::pallet]
pub mod pallet {
	// Import various types used to declare pallet in scope.
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use super::*;

	/// Our pallet's configuration trait. All our types and constants go in here. If the
	/// pallet is dependent on specific other pallets, then their configuration traits
	/// should be added to our implied traits list.
	///
	/// `frame_system::Config` should always be included.
	#[pallet::config]
	pub trait Config: pallet_balances::Config + frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
		/// A dispatchable call.
		type Call: Parameter + Dispatchable<Origin=Self::Origin> + GetDispatchInfo + From<frame_system::Call<Self>>;
		/// The currency trait.
		type Currency: ReservableCurrency<Self::AccountId>;
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Insufficient account balance.
		InsufficientFunds,
		/// Invalid configuration.
		NotConfigured,
		/// Renewed extrinsic is not found.
		RenewedNotFound,
		/// Attempting to store empty transaction
		EmptyTransaction,
		/// Proof was not expected in this block.
		UnexpectedProof,
		/// Proof failed verification.
		InvalidProof,
		/// Missing storage proof.
		MissingProof,
		/// Unable to verify proof becasue state data is missing.
		MissingStateData,
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(_n: T::BlockNumber) -> Weight {
			<Counter<T>>::put(0);
			0
		}

		fn on_finalize(n: T::BlockNumber) {
			<TransactionCount<T>>::insert(n, <Counter<T>>::get().unwrap_or(0));
			// Drop obsolete roots
			<Counter<T>>::kill();
			let period = <StoragePeriod<T>>::get().unwrap();
			let obsolete = n.saturating_sub(period);
			if obsolete > Zero::zero() {
				<TransactionRoots<T>>::remove_prefix(obsolete);
				<TransactionCount<T>>::remove(obsolete);
			}
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(1)]
		pub(super) fn store(
			origin: OriginFor<T>,
			data: Vec<u8>,
		) -> DispatchResultWithPostInfo {
			ensure!(data.len() > 0, Error::<T>::EmptyTransaction);
			Self::apply_fee(origin, data.len() as u32)?;

			// Chunk data and compute storage root
			let chunks = data.chunks(CHUNK_SIZE).map(|c| c.to_vec()).collect();
			let root = sp_io::trie::blake2_256_ordered_root(chunks);

			let content_hash = sp_io::hashing::blake2_256(&data);
			let extrinsic_index = <frame_system::Pallet<T>>::extrinsic_index().unwrap();
			sp_io::transaction_index::index(extrinsic_index, data.len() as u32, content_hash);

			let block_num = <frame_system::Pallet<T>>::block_number();
			let mut counter = <Counter<T>>::get().unwrap_or(0);
			<TransactionRoots<T>>::insert(block_num, counter, TransactionInfo {
				chunk_root: root,
				size: data.len() as u32,
				content_hash: content_hash.into(),
			});
			counter += 1;
			<Counter<T>>::put(counter);

			Self::deposit_event(Event::Stored);
			Ok(().into())
		}

		#[pallet::weight(1)]
		pub(super) fn renew(
			origin: OriginFor<T>,
			block: T::BlockNumber,
			index: u32,
		) -> DispatchResultWithPostInfo {
			let info = <TransactionRoots<T>>::get(block, index).ok_or(Error::<T>::RenewedNotFound)?;
			Self::apply_fee(origin, info.size)?;

			let extrinsic_index = <frame_system::Pallet<T>>::extrinsic_index().unwrap();
			sp_io::transaction_index::renew(extrinsic_index, info.content_hash.into());

			let mut counter = <Counter<T>>::get().unwrap_or(0);
			let block_num = <frame_system::Pallet<T>>::block_number();
			<TransactionRoots<T>>::insert(block_num, counter, info);
			counter += 1;
			<Counter<T>>::put(counter);

			Self::deposit_event(Event::Renewed);
			Ok(().into())
		}

		#[pallet::weight(1)]
		fn check_proof(
			origin: OriginFor<T>,
			proof: Option<StorageProof>,
		) -> DispatchResultWithPostInfo {
			ensure_none(origin)?;
			let number = <frame_system::Pallet<T>>::block_number();
			let period = <StoragePeriod<T>>::get().unwrap();
			let target_number = number.saturating_sub(period);
			if target_number.is_zero() {
				ensure!(proof.is_none(), Error::<T>::UnexpectedProof);
				return Ok(().into())
			}
			let transaction_count = <TransactionCount<T>>::get(target_number);
			let mut total_chunks = 0;
			for t in 0 .. transaction_count {
				match <TransactionRoots<T>>::get(target_number, t) {
					Some(info) => total_chunks += ((info.size as u64 + CHUNK_SIZE as u64 - 1) / CHUNK_SIZE as u64) as u32,
					None => break,
				}
			}
			if total_chunks == 0 {
				ensure!(proof.is_none(), Error::<T>::UnexpectedProof);
				return Ok(().into())
			}
			let proof = proof.ok_or_else(|| Error::<T>::MissingProof)?;
			let parent_hash = <frame_system::Pallet<T>>::parent_hash();
			let selected_chunk_index = sp_storage_proof::random_chunk(parent_hash.as_ref(), total_chunks);
			total_chunks = 0;
			let mut t = 0;
			let (info, chunk_index) = loop {
				match <TransactionRoots<T>>::get(target_number, t) {
					Some(info) => {
						total_chunks += ((info.size as u64 + CHUNK_SIZE as u64 - 1) / CHUNK_SIZE as u64) as u32;
						if total_chunks >= selected_chunk_index {
							break (info, total_chunks - selected_chunk_index)
						}
					},
					None => Err(Error::<T>::MissingStateData)?,
				}
				t += 1;
			};

			ensure!(
				sp_io::trie::blake2_256_verity_proof(
					info.chunk_root,
					&proof.proof,
					&(chunk_index as u32).to_be_bytes(),
					&proof.chunk,
				),
				Error::<T>::InvalidProof
			);
			Ok(().into())
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		Stored,
		Renewed,
	}

	/// Collection of extrinsic storage roots for the current block.
	#[pallet::storage]
	#[pallet::getter(fn transaction_roots)]
	pub(super) type TransactionRoots<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::BlockNumber,
		Blake2_128Concat,
		u32,
		TransactionInfo,
		OptionQuery,
	>;

	/// Count indexed chunks for each block.
	#[pallet::storage]
	pub(super) type TransactionCount<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::BlockNumber,
		u32,
		ValueQuery,
	>;

	#[pallet::storage]
	#[pallet::getter(fn byte_fee)]
	pub(super) type ByteFee<T: Config> = StorageValue<_, BalanceOf<T>>;

	#[pallet::storage]
	pub(super) type Counter<T: Config> = StorageValue<_, u32>;

	#[pallet::storage]
	pub(super) type StoragePeriod<T: Config> = StorageValue<_, T::BlockNumber>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub byte_fee: BalanceOf<T>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			Self {
				byte_fee: 10u32.into(),
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			<ByteFee<T>>::put(&self.byte_fee);
		}
	}

	#[pallet::inherent]
	impl<T: Config> ProvideInherent for Pallet<T> {
		type Call = Call<T>;
		type Error = sp_storage_proof::InherentError;
		const INHERENT_IDENTIFIER: InherentIdentifier = sp_storage_proof::INHERENT_IDENTIFIER;

		fn create_inherent(data: &InherentData) -> Option<Self::Call> {
			let proof = data.get_data::<StorageProof>(&Self::INHERENT_IDENTIFIER).unwrap_or(None);
			Some(Call::check_proof(proof))
		}

		fn check_inherent(_call: &Self::Call, _data: &InherentData) -> result::Result<(), Self::Error> {
			Ok(())
		}

		fn is_inherent(call: &Self::Call) -> bool {
			matches!(call, Call::check_proof(_))
		}
	}

	impl<T: Config> Pallet<T> {
		fn apply_fee(origin: OriginFor<T>, size: u32) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let byte_fee = ByteFee::<T>::get().ok_or(Error::<T>::NotConfigured)?;
			let fee = byte_fee.saturating_mul(size.into());
			ensure!(T::Currency::can_slash(&sender, fee), Error::<T>::InsufficientFunds);
			T::Currency::slash(&sender, fee);
			Ok(())
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use frame_support::{
		assert_ok, parameter_types,
		weights::{DispatchInfo, GetDispatchInfo}, traits::{OnInitialize, OnFinalize}
	};
	use sp_core::H256;
	// The testing primitives are very useful for avoiding having to work with signatures
	// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
	use sp_runtime::{
		testing::Header, BuildStorage,
		traits::{BlakeTwo256, IdentityLookup},
	};
	// Reexport crate as its pallet name for construct_runtime.
	use crate as pallet_transaction_storage;

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
	type Block = frame_system::mocking::MockBlock<Test>;

	// For testing the pallet, we construct a mock runtime.
	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
			Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
			TransactionStorage: pallet_transaction_storage::{Pallet, Call, Storage, Config<T>, Inherent, Event<T>},
		}
	);

	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub BlockWeights: frame_system::limits::BlockWeights =
			frame_system::limits::BlockWeights::simple_max(1024);
	}
	impl frame_system::Config for Test {
		type BaseCallFilter = ();
		type BlockWeights = ();
		type BlockLength = ();
		type DbWeight = ();
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = Call;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = Event;
		type BlockHashCount = BlockHashCount;
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 1;
	}
	impl pallet_balances::Config for Test {
		type MaxLocks = ();
		type Balance = u64;
		type DustRemoval = ();
		type Event = Event;
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
		type WeightInfo = ();
	}
	impl Config for Test {
		type Event = Event;
		type Call = Call;
		type Currency = Balances;
	}

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	pub fn new_test_ext() -> sp_io::TestExternalities {
		let t = GenesisConfig {
			// We use default for brevity, but you can configure as desired if needed.
			frame_system: Default::default(),
			pallet_balances: Default::default(),
			pallet_transaction_storage: pallet_transaction_storage::GenesisConfig::default(),
		}.build_storage().unwrap();
		t.into()
	}

	#[test]
	fn stores_transaction() {
		let mut ext = new_test_ext();
		let data = vec![1u8, 2u8, 3u8];
		ext.execute_with(|| {
			assert_ok!(TransactionStorage::store(Origin::signed(1), data));
		});
		assert!(ext.overlayed_changes().transaction_index_ops().len() == 1);
	}
}
