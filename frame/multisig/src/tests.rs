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

// Tests for Multisig Pallet

#![cfg(test)]

use super::*;

use frame_support::{
	assert_ok, assert_noop, impl_outer_origin, parameter_types, impl_outer_dispatch,
	weights::Weight, impl_outer_event
};
use sp_core::H256;
use sp_runtime::{Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header};
use crate as multisig;

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

impl_outer_event! {
	pub enum TestEvent for Test {
		system<T>,
		pallet_balances<T>,
		multisig<T>,
	}
}
impl_outer_dispatch! {
	pub enum Call for Test where origin: Origin {
		frame_system::System,
		pallet_balances::Balances,
		multisig::Multisig,
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
}
parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}
impl pallet_balances::Trait for Test {
	type Balance = u64;
	type Event = TestEvent;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
}
parameter_types! {
	pub const DepositBase: u64 = 1;
	pub const DepositFactor: u64 = 1;
	pub const MaxSignatories: u16 = 3;
}
pub struct TestIsCallable;
impl Filter<Call> for TestIsCallable {
	fn filter(c: &Call) -> bool {
		match *c {
			Call::Balances(_) => true,
			// Needed for benchmarking
			Call::System(frame_system::Call::remark(_)) => true,
			_ => false,
		}
	}
}
impl FilterStack<Call> for TestIsCallable {
	type Stack = ();
	fn push(_: impl Fn(&Call) -> bool + 'static) {}
	fn pop() {}
	fn take() -> Self::Stack { () }
	fn restore(_: Self::Stack) {}
}
impl Trait for Test {
	type Event = TestEvent;
	type Call = Call;
	type Currency = Balances;
	type DepositBase = DepositBase;
	type DepositFactor = DepositFactor;
	type MaxSignatories = MaxSignatories;
	type IsCallable = TestIsCallable;
}
type System = frame_system::Module<Test>;
type Balances = pallet_balances::Module<Test>;
type Multisig = Module<Test>;

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
	system::Module::<Test>::events().pop().map(|e| e.event).expect("Event expected")
}

fn expect_event<E: Into<TestEvent>>(e: E) {
	assert_eq!(last_event(), e.into());
}

fn now() -> Timepoint<u64> {
	Multisig::timepoint()
}

#[test]
fn multisig_deposit_is_taken_and_returned() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		assert_ok!(Multisig::as_multi(Origin::signed(1), 2, vec![2, 3], None, call.clone()));
		assert_eq!(Balances::free_balance(1), 2);
		assert_eq!(Balances::reserved_balance(1), 3);

		assert_ok!(Multisig::as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), call));
		assert_eq!(Balances::free_balance(1), 5);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn cancel_multisig_returns_deposit() {
	new_test_ext().execute_with(|| {
		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		let hash = call.using_encoded(blake2_256);
		assert_ok!(Multisig::approve_as_multi(Origin::signed(1), 3, vec![2, 3], None, hash.clone()));
		assert_ok!(Multisig::approve_as_multi(Origin::signed(2), 3, vec![1, 3], Some(now()), hash.clone()));
		assert_eq!(Balances::free_balance(1), 6);
		assert_eq!(Balances::reserved_balance(1), 4);
		assert_ok!(
			Multisig::cancel_as_multi(Origin::signed(1), 3, vec![2, 3], now(), hash.clone()),
		);
		assert_eq!(Balances::free_balance(1), 10);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn timepoint_checking_works() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		let hash = call.using_encoded(blake2_256);

		assert_noop!(
			Multisig::approve_as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), hash.clone()),
			Error::<Test>::UnexpectedTimepoint,
		);

		assert_ok!(Multisig::approve_as_multi(Origin::signed(1), 2, vec![2, 3], None, hash));

		assert_noop!(
			Multisig::as_multi(Origin::signed(2), 2, vec![1, 3], None, call.clone()),
			Error::<Test>::NoTimepoint,
		);
		let later = Timepoint { index: 1, .. now() };
		assert_noop!(
			Multisig::as_multi(Origin::signed(2), 2, vec![1, 3], Some(later), call.clone()),
			Error::<Test>::WrongTimepoint,
		);
	});
}

#[test]
fn multisig_2_of_3_works() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		let hash = call.using_encoded(blake2_256);
		assert_ok!(Multisig::approve_as_multi(Origin::signed(1), 2, vec![2, 3], None, hash));
		assert_eq!(Balances::free_balance(6), 0);

		assert_ok!(Multisig::as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), call));
		assert_eq!(Balances::free_balance(6), 15);
	});
}

#[test]
fn multisig_3_of_3_works() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 3);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		let hash = call.using_encoded(blake2_256);
		assert_ok!(Multisig::approve_as_multi(Origin::signed(1), 3, vec![2, 3], None, hash.clone()));
		assert_ok!(Multisig::approve_as_multi(Origin::signed(2), 3, vec![1, 3], Some(now()), hash.clone()));
		assert_eq!(Balances::free_balance(6), 0);

		assert_ok!(Multisig::as_multi(Origin::signed(3), 3, vec![1, 2], Some(now()), call));
		assert_eq!(Balances::free_balance(6), 15);
	});
}

#[test]
fn cancel_multisig_works() {
	new_test_ext().execute_with(|| {
		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		let hash = call.using_encoded(blake2_256);
		assert_ok!(Multisig::approve_as_multi(Origin::signed(1), 3, vec![2, 3], None, hash.clone()));
		assert_ok!(Multisig::approve_as_multi(Origin::signed(2), 3, vec![1, 3], Some(now()), hash.clone()));
		assert_noop!(
			Multisig::cancel_as_multi(Origin::signed(2), 3, vec![1, 3], now(), hash.clone()),
			Error::<Test>::NotOwner,
		);
		assert_ok!(
			Multisig::cancel_as_multi(Origin::signed(1), 3, vec![2, 3], now(), hash.clone()),
		);
	});
}

#[test]
fn multisig_2_of_3_as_multi_works() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		assert_ok!(Multisig::as_multi(Origin::signed(1), 2, vec![2, 3], None, call.clone()));
		assert_eq!(Balances::free_balance(6), 0);

		assert_ok!(Multisig::as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), call));
		assert_eq!(Balances::free_balance(6), 15);
	});
}

#[test]
fn multisig_2_of_3_as_multi_with_many_calls_works() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call1 = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
		let call2 = Box::new(Call::Balances(BalancesCall::transfer(7, 5)));

		assert_ok!(Multisig::as_multi(Origin::signed(1), 2, vec![2, 3], None, call1.clone()));
		assert_ok!(Multisig::as_multi(Origin::signed(2), 2, vec![1, 3], None, call2.clone()));
		assert_ok!(Multisig::as_multi(Origin::signed(3), 2, vec![1, 2], Some(now()), call2));
		assert_ok!(Multisig::as_multi(Origin::signed(3), 2, vec![1, 2], Some(now()), call1));

		assert_eq!(Balances::free_balance(6), 10);
		assert_eq!(Balances::free_balance(7), 5);
	});
}

#[test]
fn multisig_2_of_3_cannot_reissue_same_call() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
		assert_ok!(Multisig::as_multi(Origin::signed(1), 2, vec![2, 3], None, call.clone()));
		assert_ok!(Multisig::as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), call.clone()));
		assert_eq!(Balances::free_balance(multi), 5);

		assert_ok!(Multisig::as_multi(Origin::signed(1), 2, vec![2, 3], None, call.clone()));
		assert_ok!(Multisig::as_multi(Origin::signed(3), 2, vec![1, 2], Some(now()), call.clone()));

		let err = DispatchError::from(BalancesError::<Test, _>::InsufficientBalance).stripped();
		expect_event(RawEvent::MultisigExecuted(3, now(), multi, call.using_encoded(blake2_256), Err(err)));
	});
}

#[test]
fn zero_threshold_fails() {
	new_test_ext().execute_with(|| {
		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		assert_noop!(
			Multisig::as_multi(Origin::signed(1), 0, vec![2], None, call),
			Error::<Test>::ZeroThreshold,
		);
	});
}

#[test]
fn too_many_signatories_fails() {
	new_test_ext().execute_with(|| {
		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		assert_noop!(
			Multisig::as_multi(Origin::signed(1), 2, vec![2, 3, 4], None, call.clone()),
			Error::<Test>::TooManySignatories,
		);
	});
}

#[test]
fn duplicate_approvals_are_ignored() {
	new_test_ext().execute_with(|| {
		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		let hash = call.using_encoded(blake2_256);
		assert_ok!(Multisig::approve_as_multi(Origin::signed(1), 2, vec![2, 3], None, hash.clone()));
		assert_noop!(
			Multisig::approve_as_multi(Origin::signed(1), 2, vec![2, 3], Some(now()), hash.clone()),
			Error::<Test>::AlreadyApproved,
		);
		assert_ok!(Multisig::approve_as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), hash.clone()));
		assert_noop!(
			Multisig::approve_as_multi(Origin::signed(3), 2, vec![1, 2], Some(now()), hash.clone()),
			Error::<Test>::NoApprovalsNeeded,
		);
	});
}

#[test]
fn multisig_1_of_3_works() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 1);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		let hash = call.using_encoded(blake2_256);
		assert_noop!(
			Multisig::approve_as_multi(Origin::signed(1), 1, vec![2, 3], None, hash.clone()),
			Error::<Test>::NoApprovalsNeeded,
		);
		assert_noop!(
			Multisig::as_multi(Origin::signed(4), 1, vec![2, 3], None, call.clone()),
			BalancesError::<Test, _>::InsufficientBalance,
		);
		assert_ok!(Multisig::as_multi(Origin::signed(1), 1, vec![2, 3], None, call));

		assert_eq!(Balances::free_balance(6), 15);
	});
}

#[test]
fn multisig_filters() {
	new_test_ext().execute_with(|| {
		let call = Box::new(Call::System(frame_system::Call::set_code(vec![])));
		assert_noop!(
			Multisig::as_multi(Origin::signed(1), 1, vec![], None, call.clone()),
			Error::<Test>::Uncallable,
		);
	});
}
