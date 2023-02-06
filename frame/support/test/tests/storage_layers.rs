// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use frame_support::{
	assert_noop, assert_ok, dispatch::DispatchResult, pallet_prelude::ConstU32,
	storage::with_storage_layer,
};
use pallet::*;
use sp_io::TestExternalities;

#[frame_support::pallet]
pub mod pallet {
	use frame_support::{ensure, pallet_prelude::*};
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::storage]
	pub type Value<T> = StorageValue<_, u32, ValueQuery>;

	#[pallet::storage]
	pub type Map<T> = StorageMap<_, Blake2_128Concat, u32, u32, ValueQuery>;

	#[pallet::error]
	pub enum Error<T> {
		Revert,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		#[pallet::weight(1)]
		pub fn set_value(_origin: OriginFor<T>, value: u32) -> DispatchResult {
			Value::<T>::put(value);
			ensure!(value != 1, Error::<T>::Revert);
			Ok(())
		}
	}
}

pub mod decl_pallet {
	pub trait Config: frame_system::Config {}

	frame_support::decl_module! {
		pub struct Module<T: Config> for enum Call where origin: T::RuntimeOrigin {
			#[weight = 0]
			pub fn set_value(_origin, value: u32) {
				DeclValue::put(value);
				frame_support::ensure!(value != 1, "Revert!");
			}
		}
	}

	frame_support::decl_storage! {
		trait Store for Module<T: Config> as StorageTransactions {
			pub DeclValue: u32;
		}
	}
}

pub type BlockNumber = u64;
pub type Index = u64;
pub type Header = sp_runtime::generic::Header<u32, sp_runtime::traits::BlakeTwo256>;
pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<u32, RuntimeCall, (), ()>;

impl frame_system::Config for Runtime {
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type BaseCallFilter = frame_support::traits::Everything;
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = u32;
	type RuntimeCall = RuntimeCall;
	type Hash = sp_runtime::testing::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU32<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

impl pallet::Config for Runtime {}

impl decl_pallet::Config for Runtime {}

frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_system,
		MyPallet: pallet,
		DeclPallet: decl_pallet::{Call, Storage},
	}
);

#[test]
fn storage_layer_basic_commit() {
	TestExternalities::default().execute_with(|| {
		assert_eq!(Value::<Runtime>::get(), 0);
		assert!(!Map::<Runtime>::contains_key(0));

		assert_ok!(with_storage_layer(|| -> DispatchResult {
			Value::<Runtime>::set(99);
			Map::<Runtime>::insert(0, 99);
			assert_eq!(Value::<Runtime>::get(), 99);
			assert_eq!(Map::<Runtime>::get(0), 99);
			Ok(())
		}));

		assert_eq!(Value::<Runtime>::get(), 99);
		assert_eq!(Map::<Runtime>::get(0), 99);
	});
}

#[test]
fn storage_layer_basic_rollback() {
	TestExternalities::default().execute_with(|| {
		assert_eq!(Value::<Runtime>::get(), 0);
		assert_eq!(Map::<Runtime>::get(0), 0);

		assert_noop!(
			with_storage_layer(|| -> DispatchResult {
				Value::<Runtime>::set(99);
				Map::<Runtime>::insert(0, 99);
				assert_eq!(Value::<Runtime>::get(), 99);
				assert_eq!(Map::<Runtime>::get(0), 99);
				Err("revert".into())
			}),
			"revert"
		);

		assert_eq!(Value::<Runtime>::get(), 0);
		assert_eq!(Map::<Runtime>::get(0), 0);
	});
}

#[test]
fn storage_layer_rollback_then_commit() {
	TestExternalities::default().execute_with(|| {
		Value::<Runtime>::set(1);
		Map::<Runtime>::insert(1, 1);

		assert_ok!(with_storage_layer(|| -> DispatchResult {
			Value::<Runtime>::set(2);
			Map::<Runtime>::insert(1, 2);
			Map::<Runtime>::insert(2, 2);

			assert_noop!(
				with_storage_layer(|| -> DispatchResult {
					Value::<Runtime>::set(3);
					Map::<Runtime>::insert(1, 3);
					Map::<Runtime>::insert(2, 3);
					Map::<Runtime>::insert(3, 3);

					assert_eq!(Value::<Runtime>::get(), 3);
					assert_eq!(Map::<Runtime>::get(1), 3);
					assert_eq!(Map::<Runtime>::get(2), 3);
					assert_eq!(Map::<Runtime>::get(3), 3);

					Err("revert".into())
				}),
				"revert"
			);

			assert_eq!(Value::<Runtime>::get(), 2);
			assert_eq!(Map::<Runtime>::get(1), 2);
			assert_eq!(Map::<Runtime>::get(2), 2);
			assert_eq!(Map::<Runtime>::get(3), 0);

			Ok(())
		}));

		assert_eq!(Value::<Runtime>::get(), 2);
		assert_eq!(Map::<Runtime>::get(1), 2);
		assert_eq!(Map::<Runtime>::get(2), 2);
		assert_eq!(Map::<Runtime>::get(3), 0);
	});
}

#[test]
fn storage_layer_commit_then_rollback() {
	TestExternalities::default().execute_with(|| {
		Value::<Runtime>::set(1);
		Map::<Runtime>::insert(1, 1);

		assert_noop!(
			with_storage_layer(|| -> DispatchResult {
				Value::<Runtime>::set(2);
				Map::<Runtime>::insert(1, 2);
				Map::<Runtime>::insert(2, 2);

				assert_ok!(with_storage_layer(|| -> DispatchResult {
					Value::<Runtime>::set(3);
					Map::<Runtime>::insert(1, 3);
					Map::<Runtime>::insert(2, 3);
					Map::<Runtime>::insert(3, 3);

					assert_eq!(Value::<Runtime>::get(), 3);
					assert_eq!(Map::<Runtime>::get(1), 3);
					assert_eq!(Map::<Runtime>::get(2), 3);
					assert_eq!(Map::<Runtime>::get(3), 3);

					Ok(())
				}));

				assert_eq!(Value::<Runtime>::get(), 3);
				assert_eq!(Map::<Runtime>::get(1), 3);
				assert_eq!(Map::<Runtime>::get(2), 3);
				assert_eq!(Map::<Runtime>::get(3), 3);

				Err("revert".into())
			}),
			"revert"
		);

		assert_eq!(Value::<Runtime>::get(), 1);
		assert_eq!(Map::<Runtime>::get(1), 1);
		assert_eq!(Map::<Runtime>::get(2), 0);
		assert_eq!(Map::<Runtime>::get(3), 0);
	});
}

#[test]
fn storage_layer_in_pallet_call() {
	TestExternalities::default().execute_with(|| {
		use sp_runtime::traits::Dispatchable;
		let call1 = RuntimeCall::MyPallet(pallet::Call::set_value { value: 2 });
		assert_ok!(call1.dispatch(RuntimeOrigin::signed(0)));
		assert_eq!(Value::<Runtime>::get(), 2);

		let call2 = RuntimeCall::MyPallet(pallet::Call::set_value { value: 1 });
		assert_noop!(call2.dispatch(RuntimeOrigin::signed(0)), Error::<Runtime>::Revert);
	});
}

#[test]
fn storage_layer_in_decl_pallet_call() {
	TestExternalities::default().execute_with(|| {
		use frame_support::StorageValue;
		use sp_runtime::traits::Dispatchable;

		let call1 = RuntimeCall::DeclPallet(decl_pallet::Call::set_value { value: 2 });
		assert_ok!(call1.dispatch(RuntimeOrigin::signed(0)));
		assert_eq!(decl_pallet::DeclValue::get(), 2);

		let call2 = RuntimeCall::DeclPallet(decl_pallet::Call::set_value { value: 1 });
		assert_noop!(call2.dispatch(RuntimeOrigin::signed(0)), "Revert!");
		// Calling the function directly also works with storage layers.
		assert_noop!(
			decl_pallet::Module::<Runtime>::set_value(RuntimeOrigin::signed(1), 1),
			"Revert!"
		);
	});
}
