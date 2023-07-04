// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

//! Tests.

#![cfg(test)]

use crate::{self as pallet_balances, AccountData, Config, CreditOf, Error, Pallet};
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	assert_err, assert_noop, assert_ok, assert_storage_noop,
	dispatch::{DispatchInfo, GetDispatchInfo},
	parameter_types,
	traits::{
		tokens::fungible, ConstU32, ConstU64, ConstU8, Imbalance as ImbalanceT, OnUnbalanced,
		StorageMapShim, StoredMap, WhitelistedStorageKeys,
	},
	weights::{IdentityFee, Weight},
	RuntimeDebug,
};
use frame_system::{self as system, RawOrigin};
use pallet_transaction_payment::{ChargeTransactionPayment, CurrencyAdapter, Multiplier};
use scale_info::TypeInfo;
use sp_core::{hexdisplay::HexDisplay, H256};
use sp_io;
use sp_runtime::{
	testing::Header,
	traits::{BadOrigin, IdentityLookup, SignedExtension, Zero},
	ArithmeticError, DispatchError, DispatchResult, FixedPointNumber, TokenError,
};
use std::collections::BTreeSet;

mod currency_tests;
mod dispatchable_tests;
mod fungible_conformance_tests;
mod fungible_tests;
mod reentrancy_tests;

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

#[derive(
	Encode,
	Decode,
	Copy,
	Clone,
	Eq,
	PartialEq,
	Ord,
	PartialOrd,
	MaxEncodedLen,
	TypeInfo,
	RuntimeDebug,
)]
pub enum TestId {
	Foo,
	Bar,
	Baz,
}

frame_support::construct_runtime!(
	pub struct Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		TransactionPayment: pallet_transaction_payment::{Pallet, Storage, Event<T>},
	}
);

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(
			frame_support::weights::Weight::from_parts(1024, u64::MAX),
		);
	pub static ExistentialDeposit: u64 = 1;
}
impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = BlockWeights;
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = u64;
	type RuntimeCall = RuntimeCall;
	type Hash = H256;
	type Hashing = ::sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = super::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

impl pallet_transaction_payment::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type OnChargeTransaction = CurrencyAdapter<Pallet<Test>, ()>;
	type OperationalFeeMultiplier = ConstU8<5>;
	type WeightToFee = IdentityFee<u64>;
	type LengthToFee = IdentityFee<u64>;
	type FeeMultiplierUpdate = ();
}

impl Config for Test {
	type Balance = u64;
	type DustRemoval = DustTrap;
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = TestAccountStore;
	type MaxLocks = ConstU32<50>;
	type MaxReserves = ConstU32<2>;
	type ReserveIdentifier = TestId;
	type WeightInfo = ();
	type RuntimeHoldReason = TestId;
	type FreezeIdentifier = TestId;
	type MaxFreezes = ConstU32<2>;
	type MaxHolds = ConstU32<2>;
}

#[derive(Clone)]
pub struct ExtBuilder {
	existential_deposit: u64,
	monied: bool,
	dust_trap: Option<u64>,
}
impl Default for ExtBuilder {
	fn default() -> Self {
		Self { existential_deposit: 1, monied: false, dust_trap: None }
	}
}
impl ExtBuilder {
	pub fn existential_deposit(mut self, existential_deposit: u64) -> Self {
		self.existential_deposit = existential_deposit;
		self
	}
	pub fn monied(mut self, monied: bool) -> Self {
		self.monied = monied;
		if self.existential_deposit == 0 {
			self.existential_deposit = 1;
		}
		self
	}
	pub fn dust_trap(mut self, account: u64) -> Self {
		self.dust_trap = Some(account);
		self
	}
	pub fn set_associated_consts(&self) {
		DUST_TRAP_TARGET.with(|v| v.replace(self.dust_trap));
		EXISTENTIAL_DEPOSIT.with(|v| v.replace(self.existential_deposit));
	}
	pub fn build(self) -> sp_io::TestExternalities {
		self.set_associated_consts();
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test> {
			balances: if self.monied {
				vec![
					(1, 10 * self.existential_deposit),
					(2, 20 * self.existential_deposit),
					(3, 30 * self.existential_deposit),
					(4, 40 * self.existential_deposit),
					(12, 10 * self.existential_deposit),
				]
			} else {
				vec![]
			},
		}
		.assimilate_storage(&mut t)
		.unwrap();

		let mut ext = sp_io::TestExternalities::new(t);
		ext.execute_with(|| System::set_block_number(1));
		ext
	}
	pub fn build_and_execute_with(self, f: impl Fn()) {
		let other = self.clone();
		UseSystem::set(false);
		other.build().execute_with(|| f());
		UseSystem::set(true);
		self.build().execute_with(|| f());
	}
}

parameter_types! {
	static DustTrapTarget: Option<u64> = None;
}

pub struct DustTrap;

impl OnUnbalanced<CreditOf<Test, ()>> for DustTrap {
	fn on_nonzero_unbalanced(amount: CreditOf<Test, ()>) {
		match DustTrapTarget::get() {
			None => drop(amount),
			Some(a) => {
				let result = <Balances as fungible::Balanced<_>>::resolve(&a, amount);
				debug_assert!(result.is_ok());
			},
		}
	}
}

parameter_types! {
	pub static UseSystem: bool = false;
}

type BalancesAccountStore = StorageMapShim<super::Account<Test>, u64, super::AccountData<u64>>;
type SystemAccountStore = frame_system::Pallet<Test>;

pub struct TestAccountStore;
impl StoredMap<u64, super::AccountData<u64>> for TestAccountStore {
	fn get(k: &u64) -> super::AccountData<u64> {
		if UseSystem::get() {
			<SystemAccountStore as StoredMap<_, _>>::get(k)
		} else {
			<BalancesAccountStore as StoredMap<_, _>>::get(k)
		}
	}
	fn try_mutate_exists<R, E: From<DispatchError>>(
		k: &u64,
		f: impl FnOnce(&mut Option<super::AccountData<u64>>) -> Result<R, E>,
	) -> Result<R, E> {
		if UseSystem::get() {
			<SystemAccountStore as StoredMap<_, _>>::try_mutate_exists(k, f)
		} else {
			<BalancesAccountStore as StoredMap<_, _>>::try_mutate_exists(k, f)
		}
	}
	fn mutate<R>(
		k: &u64,
		f: impl FnOnce(&mut super::AccountData<u64>) -> R,
	) -> Result<R, DispatchError> {
		if UseSystem::get() {
			<SystemAccountStore as StoredMap<_, _>>::mutate(k, f)
		} else {
			<BalancesAccountStore as StoredMap<_, _>>::mutate(k, f)
		}
	}
	fn mutate_exists<R>(
		k: &u64,
		f: impl FnOnce(&mut Option<super::AccountData<u64>>) -> R,
	) -> Result<R, DispatchError> {
		if UseSystem::get() {
			<SystemAccountStore as StoredMap<_, _>>::mutate_exists(k, f)
		} else {
			<BalancesAccountStore as StoredMap<_, _>>::mutate_exists(k, f)
		}
	}
	fn insert(k: &u64, t: super::AccountData<u64>) -> Result<(), DispatchError> {
		if UseSystem::get() {
			<SystemAccountStore as StoredMap<_, _>>::insert(k, t)
		} else {
			<BalancesAccountStore as StoredMap<_, _>>::insert(k, t)
		}
	}
	fn remove(k: &u64) -> Result<(), DispatchError> {
		if UseSystem::get() {
			<SystemAccountStore as StoredMap<_, _>>::remove(k)
		} else {
			<BalancesAccountStore as StoredMap<_, _>>::remove(k)
		}
	}
}

pub fn events() -> Vec<RuntimeEvent> {
	let evt = System::events().into_iter().map(|evt| evt.event).collect::<Vec<_>>();
	System::reset_events();
	evt
}

/// create a transaction info struct from weight. Handy to avoid building the whole struct.
pub fn info_from_weight(w: Weight) -> DispatchInfo {
	DispatchInfo { weight: w, ..Default::default() }
}

#[test]
fn weights_sane() {
	let info = crate::Call::<Test>::transfer_allow_death { dest: 10, value: 4 }.get_dispatch_info();
	assert_eq!(<() as crate::WeightInfo>::transfer_allow_death(), info.weight);

	let info = crate::Call::<Test>::force_unreserve { who: 10, amount: 4 }.get_dispatch_info();
	assert_eq!(<() as crate::WeightInfo>::force_unreserve(), info.weight);
}

#[test]
fn check_whitelist() {
	let whitelist: BTreeSet<String> = AllPalletsWithSystem::whitelisted_storage_keys()
		.iter()
		.map(|s| HexDisplay::from(&s.key).to_string())
		.collect();
	// Inactive Issuance
	assert!(whitelist.contains("c2261276cc9d1f8598ea4b6a74b15c2f1ccde6872881f893a21de93dfe970cd5"));
	// Total Issuance
	assert!(whitelist.contains("c2261276cc9d1f8598ea4b6a74b15c2f57c875e4cff74148e4628f264b974c80"));
}
