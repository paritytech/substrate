// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use crate::{AccountId, AuthorityId, BlockNumber, Runtime};
use codec::KeyedVec;
use frame_support::{pallet_prelude::*, storage};
use sp_io::hashing::blake2_256;
use sp_std::prelude::*;

const BALANCE_OF: &[u8] = b"balance:";

pub use self::pallet::*;

const LOG_TARGET: &str = "substrate_test_pallet";

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_system::pallet_prelude::*;
	use sp_core::storage::well_known_keys;
	use sp_runtime::{transaction_validity::TransactionPriority, Perbill};

	#[pallet::pallet]
	#[pallet::without_storage_info]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	// The current block number being processed. Set by `on_initialize`.
	#[pallet::storage]
	pub type Number<T: Config> = StorageValue<_, T::BlockNumber, OptionQuery>;

	#[pallet::storage]
	pub type NewAuthorities<T> = StorageValue<_, Vec<AuthorityId>, OptionQuery>;

	#[pallet::storage]
	pub type Authorities<T> = StorageValue<_, Vec<AuthorityId>, ValueQuery>;

	#[pallet::genesis_config]
	#[cfg_attr(feature = "std", derive(Default))]
	pub struct GenesisConfig {
		pub authorities: Vec<AuthorityId>,
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
		fn build(&self) {
			<Authorities<T>>::put(self.authorities.clone());
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(n: T::BlockNumber) -> Weight {
			Number::<T>::put(n);
			Weight::zero()
		}

		fn on_finalize(_n: T::BlockNumber) {}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		#[pallet::weight(100)]
		pub fn authorities_change(
			origin: OriginFor<T>,
			new_authorities: Vec<AuthorityId>,
		) -> DispatchResult {
			frame_system::ensure_signed(origin)?;
			<NewAuthorities<Runtime>>::put(new_authorities.to_vec());
			Ok(())
		}

		#[pallet::call_index(1)]
		#[pallet::weight(100)]
		pub fn include_data(origin: OriginFor<T>, _data: Vec<u8>) -> DispatchResult {
			log::trace!(target: LOG_TARGET, "include_data");
			frame_system::ensure_signed(origin)?;
			Ok(())
		}

		#[pallet::call_index(2)]
		#[pallet::weight(100)]
		pub fn storage_change_unsigned(
			_origin: OriginFor<T>,
			key: Vec<u8>,
			value: Option<Vec<u8>>,
		) -> DispatchResult {
			match value {
				Some(value) => storage::unhashed::put_raw(&key, &value),
				None => storage::unhashed::kill(&key),
			}
			Ok(())
		}

		#[pallet::call_index(3)]
		#[pallet::weight(100)]
		pub fn storage_change(
			origin: OriginFor<T>,
			key: Vec<u8>,
			value: Option<Vec<u8>>,
		) -> DispatchResult {
			frame_system::ensure_signed(origin)?;
			match value {
				Some(value) => storage::unhashed::put_raw(&key, &value),
				None => storage::unhashed::kill(&key),
			}
			Ok(())
		}

		#[pallet::call_index(4)]
		#[pallet::weight(100)]
		pub fn offchain_index_set(
			origin: OriginFor<T>,
			key: Vec<u8>,
			value: Vec<u8>,
		) -> DispatchResult {
			frame_system::ensure_signed(origin)?;
			sp_io::offchain_index::set(&key, &value);
			Ok(())
		}

		#[pallet::call_index(5)]
		#[pallet::weight(100)]
		pub fn offchain_index_clear(origin: OriginFor<T>, key: Vec<u8>) -> DispatchResult {
			frame_system::ensure_signed(origin)?;
			sp_io::offchain_index::clear(&key);
			Ok(())
		}

		#[pallet::call_index(6)]
		#[pallet::weight(100)]
		pub fn store(origin: OriginFor<T>, data: Vec<u8>) -> DispatchResult {
			frame_system::ensure_signed(origin)?;
			let content_hash = sp_io::hashing::blake2_256(&data);
			let extrinsic_index: u32 =
				storage::unhashed::get(well_known_keys::EXTRINSIC_INDEX).unwrap();
			sp_io::transaction_index::index(extrinsic_index, data.len() as u32, content_hash);
			Ok(())
		}

		#[pallet::call_index(7)]
		#[pallet::weight(100)]
		pub fn deposit_log_digest_item(
			_origin: OriginFor<T>,
			log: sp_runtime::generic::DigestItem,
		) -> DispatchResult {
			<frame_system::Pallet<T>>::deposit_log(log);
			Ok(())
		}

		#[pallet::call_index(8)]
		#[pallet::weight(100)]
		pub fn call_with_priority(
			_origin: OriginFor<T>,
			_priority: TransactionPriority,
		) -> DispatchResult {
			Ok(())
		}

		#[pallet::call_index(9)]
		#[pallet::weight(100)]
		pub fn call_do_not_propagate(_origin: OriginFor<T>) -> DispatchResult {
			Ok(())
		}

		#[pallet::call_index(10)]
		#[pallet::weight(*_ratio * T::BlockWeights::get().max_block)]
		pub fn fill_block(origin: OriginFor<T>, _ratio: Perbill) -> DispatchResult {
			ensure_signed(origin)?;
			Ok(())
		}
	}

	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T> {
		type Call = Call<T>;

		fn validate_unsigned(_source: TransactionSource, call: &Self::Call) -> TransactionValidity {
			log::trace!(target: LOG_TARGET, "validate_unsigned {call:?}");
			match call {
				// offchain testing requires unsigned include_data
				Call::include_data { .. } => Ok(ValidTransaction { ..Default::default() }),

				// consensus tests do not use signer and nonce:
				Call::deposit_log_digest_item { .. } => Ok(Default::default()),

				// some tests do not need to be complicated with signer and nonce, they also need reproducible block
				// hash so no signature is allowed for this call
				Call::storage_change_unsigned { .. } => Ok(Default::default()),

				_ => Err(TransactionValidityError::Invalid(InvalidTransaction::Call)),
			}
		}
	}
}

pub fn balance_of_key(who: AccountId) -> Vec<u8> {
	who.to_keyed_vec(BALANCE_OF)
}

pub fn balance_of(who: AccountId) -> u64 {
	storage::hashed::get_or(&blake2_256, &balance_of_key(who), 0)
}

pub fn authorities() -> Vec<AuthorityId> {
	<Authorities<Runtime>>::get()
}

pub fn get_block_number() -> Option<BlockNumber> {
	<Number<Runtime>>::get()
}

use sp_runtime::transaction_validity::{
	InvalidTransaction, TransactionSource, TransactionValidity, ValidTransaction,
};

pub fn validate_runtime_call<T: pallet::Config>(call: &pallet::Call<T>) -> TransactionValidity {
	log::trace!(target: LOG_TARGET, "validate_runtime_call {call:?}");
	match call {
		Call::call_do_not_propagate {} =>
			Ok(ValidTransaction { propagate: false, ..Default::default() }),
		Call::call_with_priority { priority } =>
			Ok(ValidTransaction { priority: *priority, ..Default::default() }),
		_ => Ok(Default::default()),
	}
}
