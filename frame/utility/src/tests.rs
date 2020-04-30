// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

// Tests for Utility Pallet

#![cfg(test)]

use super::*;

use frame_support::{
	assert_ok, assert_noop, impl_outer_origin, parameter_types, impl_outer_dispatch,
	weights::Weight, impl_outer_event
};
use sp_core::H256;
use sp_runtime::{Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header};
use crate as utility;

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

impl_outer_event! {
	pub enum TestEvent for Test {
		system<T>,
		pallet_balances<T>,
		utility<T>,
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
	pub const MultisigDepositBase: u64 = 1;
	pub const MultisigDepositFactor: u64 = 1;
	pub const MaxSignatories: u16 = 3;
}
impl Trait for Test {
	type Event = TestEvent;
	type Call = Call;
	type Currency = Balances;
	type MultisigDepositBase = MultisigDepositBase;
	type MultisigDepositFactor = MultisigDepositFactor;
	type MaxSignatories = MaxSignatories;
}
type System = frame_system::Module<Test>;
type Balances = pallet_balances::Module<Test>;
type Utility = Module<Test>;

use pallet_balances::Call as BalancesCall;
use pallet_balances::Error as BalancesError;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test> {
		balances: vec![(1, 10), (2, 10), (3, 10), (4, 10), (5, 10)],
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
	Utility::timepoint()
}

#[test]
fn multisig_deposit_is_taken_and_returned() {
	new_test_ext().execute_with(|| {
		let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		assert_ok!(Utility::as_multi(Origin::signed(1), 2, vec![2, 3], None, call.clone()));
		assert_eq!(Balances::free_balance(1), 2);
		assert_eq!(Balances::reserved_balance(1), 3);

		assert_ok!(Utility::as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), call));
		assert_eq!(Balances::free_balance(1), 5);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn cancel_multisig_returns_deposit() {
	new_test_ext().execute_with(|| {
		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		let hash = call.using_encoded(blake2_256);
		assert_ok!(Utility::approve_as_multi(Origin::signed(1), 3, vec![2, 3], None, hash.clone()));
		assert_ok!(Utility::approve_as_multi(Origin::signed(2), 3, vec![1, 3], Some(now()), hash.clone()));
		assert_eq!(Balances::free_balance(1), 6);
		assert_eq!(Balances::reserved_balance(1), 4);
		assert_ok!(
			Utility::cancel_as_multi(Origin::signed(1), 3, vec![2, 3], now(), hash.clone()),
		);
		assert_eq!(Balances::free_balance(1), 10);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn timepoint_checking_works() {
	new_test_ext().execute_with(|| {
		let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		let hash = call.using_encoded(blake2_256);

		assert_noop!(
			Utility::approve_as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), hash.clone()),
			Error::<Test>::UnexpectedTimepoint,
		);

		assert_ok!(Utility::approve_as_multi(Origin::signed(1), 2, vec![2, 3], None, hash));

		assert_noop!(
			Utility::as_multi(Origin::signed(2), 2, vec![1, 3], None, call.clone()),
			Error::<Test>::NoTimepoint,
		);
		let later = Timepoint { index: 1, .. now() };
		assert_noop!(
			Utility::as_multi(Origin::signed(2), 2, vec![1, 3], Some(later), call.clone()),
			Error::<Test>::WrongTimepoint,
		);
	});
}

#[test]
fn multisig_2_of_3_works() {
	new_test_ext().execute_with(|| {
		let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		let hash = call.using_encoded(blake2_256);
		assert_ok!(Utility::approve_as_multi(Origin::signed(1), 2, vec![2, 3], None, hash));
		assert_eq!(Balances::free_balance(6), 0);

		assert_ok!(Utility::as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), call));
		assert_eq!(Balances::free_balance(6), 15);
	});
}

#[test]
fn multisig_3_of_3_works() {
	new_test_ext().execute_with(|| {
		let multi = Utility::multi_account_id(&[1, 2, 3][..], 3);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		let hash = call.using_encoded(blake2_256);
		assert_ok!(Utility::approve_as_multi(Origin::signed(1), 3, vec![2, 3], None, hash.clone()));
		assert_ok!(Utility::approve_as_multi(Origin::signed(2), 3, vec![1, 3], Some(now()), hash.clone()));
		assert_eq!(Balances::free_balance(6), 0);

		assert_ok!(Utility::as_multi(Origin::signed(3), 3, vec![1, 2], Some(now()), call));
		assert_eq!(Balances::free_balance(6), 15);
	});
}

#[test]
fn cancel_multisig_works() {
	new_test_ext().execute_with(|| {
		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		let hash = call.using_encoded(blake2_256);
		assert_ok!(Utility::approve_as_multi(Origin::signed(1), 3, vec![2, 3], None, hash.clone()));
		assert_ok!(Utility::approve_as_multi(Origin::signed(2), 3, vec![1, 3], Some(now()), hash.clone()));
		assert_noop!(
			Utility::cancel_as_multi(Origin::signed(2), 3, vec![1, 3], now(), hash.clone()),
			Error::<Test>::NotOwner,
		);
		assert_ok!(
			Utility::cancel_as_multi(Origin::signed(1), 3, vec![2, 3], now(), hash.clone()),
		);
	});
}

#[test]
fn multisig_2_of_3_as_multi_works() {
	new_test_ext().execute_with(|| {
		let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		assert_ok!(Utility::as_multi(Origin::signed(1), 2, vec![2, 3], None, call.clone()));
		assert_eq!(Balances::free_balance(6), 0);

		assert_ok!(Utility::as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), call));
		assert_eq!(Balances::free_balance(6), 15);
	});
}

#[test]
fn multisig_2_of_3_as_multi_with_many_calls_works() {
	new_test_ext().execute_with(|| {
		let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call1 = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
		let call2 = Box::new(Call::Balances(BalancesCall::transfer(7, 5)));

		assert_ok!(Utility::as_multi(Origin::signed(1), 2, vec![2, 3], None, call1.clone()));
		assert_ok!(Utility::as_multi(Origin::signed(2), 2, vec![1, 3], None, call2.clone()));
		assert_ok!(Utility::as_multi(Origin::signed(3), 2, vec![1, 2], Some(now()), call2));
		assert_ok!(Utility::as_multi(Origin::signed(3), 2, vec![1, 2], Some(now()), call1));

		assert_eq!(Balances::free_balance(6), 10);
		assert_eq!(Balances::free_balance(7), 5);
	});
}

#[test]
fn multisig_2_of_3_cannot_reissue_same_call() {
	new_test_ext().execute_with(|| {
		let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
		assert_ok!(Utility::as_multi(Origin::signed(1), 2, vec![2, 3], None, call.clone()));
		assert_ok!(Utility::as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), call.clone()));
		assert_eq!(Balances::free_balance(multi), 5);

		assert_ok!(Utility::as_multi(Origin::signed(1), 2, vec![2, 3], None, call.clone()));
		assert_ok!(Utility::as_multi(Origin::signed(3), 2, vec![1, 2], Some(now()), call.clone()));

		let err = DispatchError::from(BalancesError::<Test, _>::InsufficientBalance).stripped();
		expect_event(RawEvent::MultisigExecuted(3, now(), multi, call.using_encoded(blake2_256), Err(err)));
	});
}

#[test]
fn zero_threshold_fails() {
	new_test_ext().execute_with(|| {
		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		assert_noop!(
			Utility::as_multi(Origin::signed(1), 0, vec![2], None, call),
			Error::<Test>::ZeroThreshold,
		);
	});
}

#[test]
fn too_many_signatories_fails() {
	new_test_ext().execute_with(|| {
		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		assert_noop!(
			Utility::as_multi(Origin::signed(1), 2, vec![2, 3, 4], None, call.clone()),
			Error::<Test>::TooManySignatories,
		);
	});
}

#[test]
fn duplicate_approvals_are_ignored() {
	new_test_ext().execute_with(|| {
		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		let hash = call.using_encoded(blake2_256);
		assert_ok!(Utility::approve_as_multi(Origin::signed(1), 2, vec![2, 3], None, hash.clone()));
		assert_noop!(
			Utility::approve_as_multi(Origin::signed(1), 2, vec![2, 3], Some(now()), hash.clone()),
			Error::<Test>::AlreadyApproved,
		);
		assert_ok!(Utility::approve_as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), hash.clone()));
		assert_noop!(
			Utility::approve_as_multi(Origin::signed(3), 2, vec![1, 2], Some(now()), hash.clone()),
			Error::<Test>::NoApprovalsNeeded,
		);
	});
}

#[test]
fn multisig_1_of_3_works() {
	new_test_ext().execute_with(|| {
		let multi = Utility::multi_account_id(&[1, 2, 3][..], 1);
		assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
		let hash = call.using_encoded(blake2_256);
		assert_noop!(
			Utility::approve_as_multi(Origin::signed(1), 1, vec![2, 3], None, hash.clone()),
			Error::<Test>::NoApprovalsNeeded,
		);
		assert_noop!(
			Utility::as_multi(Origin::signed(4), 1, vec![2, 3], None, call.clone()),
			BalancesError::<Test, _>::InsufficientBalance,
		);
		assert_ok!(Utility::as_multi(Origin::signed(1), 1, vec![2, 3], None, call));

		assert_eq!(Balances::free_balance(6), 15);
	});
}

#[test]
fn as_sub_works() {
	new_test_ext().execute_with(|| {
		let sub_1_0 = Utility::sub_account_id(1, 0);
		assert_ok!(Balances::transfer(Origin::signed(1), sub_1_0, 5));
		assert_noop!(Utility::as_sub(
			Origin::signed(1),
			1,
			Box::new(Call::Balances(BalancesCall::transfer(6, 3))),
		), BalancesError::<Test, _>::InsufficientBalance);
		assert_ok!(Utility::as_sub(
			Origin::signed(1),
			0,
			Box::new(Call::Balances(BalancesCall::transfer(2, 3))),
		));
		assert_eq!(Balances::free_balance(sub_1_0), 2);
		assert_eq!(Balances::free_balance(2), 13);
	});
}

#[test]
fn batch_with_root_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Balances::free_balance(1), 10);
		assert_eq!(Balances::free_balance(2), 10);
		assert_ok!(Utility::batch(Origin::ROOT, vec![
			Call::Balances(BalancesCall::force_transfer(1, 2, 5)),
			Call::Balances(BalancesCall::force_transfer(1, 2, 5))
		]));
		assert_eq!(Balances::free_balance(1), 0);
		assert_eq!(Balances::free_balance(2), 20);
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
