// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

// Tests for Utility Pallet

#![cfg(test)]

use super::*;

use frame_support::{
	assert_ok, assert_noop, impl_outer_origin, parameter_types, impl_outer_dispatch,
	weights::Weight, impl_outer_event, dispatch::DispatchError, traits::Filter, storage,
};
use sp_core::H256;
use sp_runtime::{Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header};
use crate as utility;

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}
impl_outer_event! {
	pub enum TestEvent for Test {
		frame_system<T>,
		pallet_balances<T>,
		utility,
	}
}
impl_outer_dispatch! {
	pub enum Call for Test where origin: Origin {
		frame_system::System,
		pallet_balances::Balances,
		utility::Utility,
	}
}

// For testing the pallet, we construct most of a mock runtime. This means
// first constructing a configuration type (`Test`) which `impl`s each of the
// configuration traits of pallets we want to use.
#[derive(Clone, Eq, PartialEq)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
impl frame_system::Trait for Test {
	type BaseCallFilter = TestBaseCallFilter;
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Call = Call;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = TestEvent;
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}
parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}
impl pallet_balances::Trait for Test {
	type Balance = u64;
	type DustRemoval = ();
	type Event = TestEvent;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}
parameter_types! {
	pub const MultisigDepositBase: u64 = 1;
	pub const MultisigDepositFactor: u64 = 1;
	pub const MaxSignatories: u16 = 3;
}
pub struct TestBaseCallFilter;
impl Filter<Call> for TestBaseCallFilter {
	fn filter(c: &Call) -> bool {
		match *c {
			Call::Balances(_) => true,
			// For benchmarking, this acts as a noop call
			Call::System(frame_system::Call::remark(..)) => true,
			_ => false,
		}
	}
}
impl Trait for Test {
	type Event = TestEvent;
	type Call = Call;
	type WeightInfo = ();
}
type System = frame_system::Module<Test>;
type Balances = pallet_balances::Module<Test>;
type Utility = Module<Test>;

use pallet_balances::Call as BalancesCall;
use pallet_balances::Error as BalancesError;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test> {
		balances: vec![(1, 10), (2, 10), (3, 10), (4, 10), (5, 2)],
	}.assimilate_storage(&mut t).unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

fn last_event() -> TestEvent {
	frame_system::Module::<Test>::events().pop().map(|e| e.event).expect("Event expected")
}

fn expect_event<E: Into<TestEvent>>(e: E) {
	assert_eq!(last_event(), e.into());
}

#[test]
fn as_derivative_works() {
	new_test_ext().execute_with(|| {
		let sub_1_0 = Utility::derivative_account_id(1, 0);
		assert_ok!(Balances::transfer(Origin::signed(1), sub_1_0, 5));
		assert_noop!(Utility::as_derivative(
			Origin::signed(1),
			1,
			Box::new(Call::Balances(BalancesCall::transfer(6, 3))),
		), BalancesError::<Test, _>::InsufficientBalance);
		assert_ok!(Utility::as_derivative(
			Origin::signed(1),
			0,
			Box::new(Call::Balances(BalancesCall::transfer(2, 3))),
		));
		assert_eq!(Balances::free_balance(sub_1_0), 2);
		assert_eq!(Balances::free_balance(2), 13);
	});
}

#[test]
fn as_derivative_filters() {
	new_test_ext().execute_with(|| {
		assert_noop!(Utility::as_derivative(
			Origin::signed(1),
			1,
			Box::new(Call::System(frame_system::Call::suicide())),
		), DispatchError::BadOrigin);
	});
}

#[test]
fn batch_with_root_works() {
	new_test_ext().execute_with(|| {
		let k = b"a".to_vec();
		let call = Call::System(frame_system::Call::set_storage(vec![(k.clone(), k.clone())]));
		assert!(!TestBaseCallFilter::filter(&call));
		assert_eq!(Balances::free_balance(1), 10);
		assert_eq!(Balances::free_balance(2), 10);
		assert_ok!(Utility::batch(Origin::root(), vec![
			Call::Balances(BalancesCall::force_transfer(1, 2, 5)),
			Call::Balances(BalancesCall::force_transfer(1, 2, 5)),
			call, // Check filters are correctly bypassed
		]));
		assert_eq!(Balances::free_balance(1), 0);
		assert_eq!(Balances::free_balance(2), 20);
		assert_eq!(storage::unhashed::get_raw(&k), Some(k));
	});
}

#[test]
fn batch_with_signed_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Balances::free_balance(1), 10);
		assert_eq!(Balances::free_balance(2), 10);
		assert_ok!(
			Utility::batch(Origin::signed(1), vec![
				Call::Balances(BalancesCall::transfer(2, 5)),
				Call::Balances(BalancesCall::transfer(2, 5))
			]),
		);
		assert_eq!(Balances::free_balance(1), 0);
		assert_eq!(Balances::free_balance(2), 20);
	});
}

#[test]
fn batch_with_signed_filters() {
	new_test_ext().execute_with(|| {
		assert_ok!(
			Utility::batch(Origin::signed(1), vec![
				Call::System(frame_system::Call::suicide())
			]),
		);
		expect_event(Event::BatchInterrupted(0, DispatchError::BadOrigin));
	});
}

#[test]
fn batch_early_exit_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Balances::free_balance(1), 10);
		assert_eq!(Balances::free_balance(2), 10);
		assert_ok!(
			Utility::batch(Origin::signed(1), vec![
				Call::Balances(BalancesCall::transfer(2, 5)),
				Call::Balances(BalancesCall::transfer(2, 10)),
				Call::Balances(BalancesCall::transfer(2, 5)),
			]),
		);
		assert_eq!(Balances::free_balance(1), 5);
		assert_eq!(Balances::free_balance(2), 15);
	});
}
