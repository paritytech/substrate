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

#[cfg(any(test, feature = "runtime-benchmarks"))]
mod mock;
#[cfg(test)]
mod tests;
mod benchmarking;
pub mod weights;

use frame_support::{
	traits::{ReservableCurrency, Currency},
	dispatch::{Dispatchable, GetDispatchInfo},
};
use sp_std::prelude::*;
use sp_std::{result};
use codec::{Encode, Decode};
use sp_runtime::traits::{Saturating, BlakeTwo256, Hash, Zero};
use sp_transaction_storage_proof::{
	TransactionStorageProof, InherentError,
	random_chunk, encode_index,
	CHUNK_SIZE, INHERENT_IDENTIFIER, DEFAULT_STORAGE_PERIOD,
};

/// A type alias for the balance type from this pallet's point of view.
type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

// Re-export pallet items so that they can be accessed from the crate namespace.
pub use pallet::*;
pub use weights::WeightInfo;

/// Maximum bytes that can be storead in one transaction.
// Increasing it further also requires raising the allocator limit.
pub const MAX_DATA_SIZE: u32 = 8 * 1024 * 1024;

#[derive(Encode, Decode, sp_runtime::RuntimeDebug, PartialEq, Eq)]
pub struct TransactionInfo {
	chunk_root: <BlakeTwo256 as Hash>::Output,
	content_hash: <BlakeTwo256 as Hash>::Output,
	size: u32,
}

#[frame_support::pallet]
pub mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
		/// A dispatchable call.
		type Call: Parameter + Dispatchable<Origin=Self::Origin> + GetDispatchInfo + From<frame_system::Call<Self>>;
		/// The currency trait.
		type Currency: ReservableCurrency<Self::AccountId>;
		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
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
			// This will be cleared in in `on_finalize`
			<Counter<T>>::put(0);
			0
		}

		fn on_finalize(n: T::BlockNumber) {
			<TransactionCount<T>>::insert(n, <Counter<T>>::get().unwrap_or(0));
			<Counter<T>>::kill();
			// Drop obsolete roots
			let period = <StoragePeriod<T>>::get().unwrap_or(DEFAULT_STORAGE_PERIOD.into());
			let obsolete = n.saturating_sub(period);
			if obsolete > Zero::zero() {
				<TransactionRoots<T>>::remove_prefix(obsolete);
				<TransactionCount<T>>::remove(obsolete);
			}
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Index and store data on chain. Minimum data size is 1 bytes, maxmum is `MAX_DATA_SIZE`.
		/// Data will be removed after `STORAGE_PERIOD` blocks, unless `renew` is called.
		/// # <weight>
		/// - n*log(n) of data size, as all data is pushed to an in-memory trie.
		/// Additionally contains a DB write.
		/// # </weight>
		#[pallet::weight(T::WeightInfo::store(data.len() as u32))]
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
			<TransactionRoots<T>>::insert(block_num, counter, TransactionInfo {
				chunk_root: root,
				size: data.len() as u32,
				content_hash: content_hash.into(),
			});
			let counter = <Counter<T>>::mutate(|c| { *c += 1; c }); 
			Self::deposit_event(Event::Stored(counter));
			Ok(().into())
		}

		/// Renew previously stored data. Parameters are the block number that contains
		/// previous `store` or `renew` call and transaction index within that block.
		/// Transaction index is emitted in the `Stored` or `Renewed` event.
		/// Applies same fees as `store`.
		/// # <weight>
		/// - Constant with a single DB read.
		/// # </weight>
		#[pallet::weight(T::WeightInfo::renew())]
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
			Self::deposit_event(Event::Renewed(counter));
			counter += 1;
			<Counter<T>>::put(counter);
			Ok(().into())
		}

		/// Check storage proof for block number `block_number() - StoragePeriod`.
		/// If such block does not exist the proof is expected to be `None`.
		/// # <weight>
		/// - Linear w.r.t the number of indexed transactions in the proved block for random probing.
		/// There's a DB read for each transaction.
		/// Here we assume a maximum of 100 probed transactions.
		/// # </weight>
		#[pallet::weight((T::WeightInfo::check_proof_max(), DispatchClass::Mandatory))]
		pub(super) fn check_proof(
			origin: OriginFor<T>,
			proof: Option<TransactionStorageProof>,
		) -> DispatchResultWithPostInfo {
			ensure_none(origin)?;
			let number = <frame_system::Pallet<T>>::block_number();
			let period = <StoragePeriod<T>>::get().unwrap_or(DEFAULT_STORAGE_PERIOD.into());
			let target_number = number.saturating_sub(period);
			if target_number.is_zero() {
				ensure!(proof.is_none(), Error::<T>::UnexpectedProof);
				return Ok(().into())
			}
			let transaction_count = <TransactionCount<T>>::get(target_number);
			let mut total_chunks = 0;
			for t in 0 .. transaction_count {
				match <TransactionRoots<T>>::get(target_number, t) {
					Some(info) => total_chunks +=
						((info.size as u64 + CHUNK_SIZE as u64 - 1) / CHUNK_SIZE as u64) as u32,
					None => break,
				}
			}
			if total_chunks == 0 {
				ensure!(proof.is_none(), Error::<T>::UnexpectedProof);
				return Ok(().into())
			}
			let proof = proof.ok_or_else(|| Error::<T>::MissingProof)?;
			let parent_hash = <frame_system::Pallet<T>>::parent_hash();
			let selected_chunk_index = random_chunk(parent_hash.as_ref(), total_chunks);
			total_chunks = 0;
			let mut t = 0;
			let (info, chunk_index) = loop {
				match <TransactionRoots<T>>::get(target_number, t) {
					Some(info) => {
						let chunks = ((info.size as u64 + CHUNK_SIZE as u64 - 1) / CHUNK_SIZE as u64) as u32;
						if total_chunks + chunks >= selected_chunk_index {
							break (info, selected_chunk_index - total_chunks)
						}
						total_chunks += chunks;
					},
					None => Err(Error::<T>::MissingStateData)?,
				}
				t += 1;
			};

			ensure!(
				sp_io::trie::blake2_256_verify_proof(
					info.chunk_root,
					&proof.proof,
					&encode_index(chunk_index),
					&proof.chunk,
				),
				Error::<T>::InvalidProof
			);
			Self::deposit_event(Event::ProofChecked);
			Ok(().into())
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Stored data under specified index.
		Stored(u32),
		/// Renewed data under specified index.
		Renewed(u32),
		/// Storage proof was successfully checked.
		ProofChecked,
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
	/// Storage fee per byte.
	pub(super) type ByteFee<T: Config> = StorageValue<_, BalanceOf<T>>;

	#[pallet::storage]
	pub(super) type Counter<T: Config> = StorageValue<_, u32, ValueQuery>;

	/// Storage period for data in blocks. Should match `sp_storage_proof::DEFAULT_STORAGE_PERIOD`
	/// for block authoring.
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
		type Error = InherentError;
		const INHERENT_IDENTIFIER: InherentIdentifier = INHERENT_IDENTIFIER;

		fn create_inherent(data: &InherentData) -> Option<Self::Call> {
			let proof = data.get_data::<TransactionStorageProof>(&Self::INHERENT_IDENTIFIER).unwrap_or(None);
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
