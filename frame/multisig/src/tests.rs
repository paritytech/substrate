// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

use crate as pallet_multisig;
use frame_support::{
	assert_noop, assert_ok, parameter_types,
	traits::{ConstU16, ConstU32, ConstU64, Contains},
};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;
type OpaqueCall = super::OpaqueCall<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Multisig: pallet_multisig::{Pallet, Call, Storage, Event<T>},
	}
);

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(frame_support::weights::Weight::from_ref_time(1024));
}
impl frame_system::Config for Test {
	type BaseCallFilter = TestBaseCallFilter;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type RuntimeCall = RuntimeCall;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = u64;
	type RuntimeEvent = RuntimeEvent;
	type DustRemoval = ();
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
}

pub struct TestBaseCallFilter;
impl Contains<RuntimeCall> for TestBaseCallFilter {
	fn contains(c: &RuntimeCall) -> bool {
		match *c {
			RuntimeCall::Balances(_) => true,
			// Needed for benchmarking
			RuntimeCall::System(frame_system::Call::remark { .. }) => true,
			_ => false,
		}
	}
}
impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type RuntimeCall = RuntimeCall;
	type Currency = Balances;
	type DepositBase = ConstU64<1>;
	type DepositFactor = ConstU64<1>;
	type MaxSignatories = ConstU16<3>;
	type WeightInfo = ();
}

use pallet_balances::{Call as BalancesCall, Error as BalancesError};

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test> {
		balances: vec![(1, 10), (2, 10), (3, 10), (4, 10), (5, 2)],
	}
	.assimilate_storage(&mut t)
	.unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

fn now() -> Timepoint<u64> {
	Multisig::timepoint()
}

fn call_transfer(dest: u64, value: u64) -> RuntimeCall {
	RuntimeCall::Balances(BalancesCall::transfer { dest, value })
}

#[test]
fn multisig_deposit_is_taken_and_returned() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(3), multi, 5));

		let call = call_transfer(6, 15);
		let call_weight = call.get_dispatch_info().weight;
		let data = call.encode();
		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(1),
			2,
			vec![2, 3],
			None,
			OpaqueCall::from_encoded(data.clone()),
			false,
			Weight::zero()
		));
		assert_eq!(Balances::free_balance(1), 2);
		assert_eq!(Balances::reserved_balance(1), 3);

		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(2),
			2,
			vec![1, 3],
			Some(now()),
			OpaqueCall::from_encoded(data),
			false,
			call_weight
		));
		assert_eq!(Balances::free_balance(1), 5);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn multisig_deposit_is_taken_and_returned_with_call_storage() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(3), multi, 5));

		let call = call_transfer(6, 15);
		let call_weight = call.get_dispatch_info().weight;
		let data = call.encode();
		let hash = blake2_256(&data);
		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(1),
			2,
			vec![2, 3],
			None,
			OpaqueCall::from_encoded(data),
			true,
			Weight::zero()
		));
		assert_eq!(Balances::free_balance(1), 0);
		assert_eq!(Balances::reserved_balance(1), 5);

		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(2),
			2,
			vec![1, 3],
			Some(now()),
			hash,
			call_weight
		));
		assert_eq!(Balances::free_balance(1), 5);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn multisig_deposit_is_taken_and_returned_with_alt_call_storage() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 3);
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(3), multi, 5));

		let call = call_transfer(6, 15);
		let call_weight = call.get_dispatch_info().weight;
		let data = call.encode();
		let hash = blake2_256(&data);

		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(1),
			3,
			vec![2, 3],
			None,
			hash,
			Weight::zero()
		));
		assert_eq!(Balances::free_balance(1), 1);
		assert_eq!(Balances::reserved_balance(1), 4);

		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(2),
			3,
			vec![1, 3],
			Some(now()),
			OpaqueCall::from_encoded(data),
			true,
			Weight::zero()
		));
		assert_eq!(Balances::free_balance(2), 3);
		assert_eq!(Balances::reserved_balance(2), 2);
		assert_eq!(Balances::free_balance(1), 1);
		assert_eq!(Balances::reserved_balance(1), 4);

		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(3),
			3,
			vec![1, 2],
			Some(now()),
			hash,
			call_weight
		));
		assert_eq!(Balances::free_balance(1), 5);
		assert_eq!(Balances::reserved_balance(1), 0);
		assert_eq!(Balances::free_balance(2), 5);
		assert_eq!(Balances::reserved_balance(2), 0);
	});
}

#[test]
fn cancel_multisig_returns_deposit() {
	new_test_ext().execute_with(|| {
		let call = call_transfer(6, 15).encode();
		let hash = blake2_256(&call);
		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(1),
			3,
			vec![2, 3],
			None,
			hash,
			Weight::zero()
		));
		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(2),
			3,
			vec![1, 3],
			Some(now()),
			hash,
			Weight::zero()
		));
		assert_eq!(Balances::free_balance(1), 6);
		assert_eq!(Balances::reserved_balance(1), 4);
		assert_ok!(Multisig::cancel_as_multi(RuntimeOrigin::signed(1), 3, vec![2, 3], now(), hash));
		assert_eq!(Balances::free_balance(1), 10);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn timepoint_checking_works() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(3), multi, 5));

		let call = call_transfer(6, 15).encode();
		let hash = blake2_256(&call);

		assert_noop!(
			Multisig::approve_as_multi(
				RuntimeOrigin::signed(2),
				2,
				vec![1, 3],
				Some(now()),
				hash,
				Weight::zero()
			),
			Error::<Test>::UnexpectedTimepoint,
		);

		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(1),
			2,
			vec![2, 3],
			None,
			hash,
			Weight::zero()
		));

		assert_noop!(
			Multisig::as_multi(
				RuntimeOrigin::signed(2),
				2,
				vec![1, 3],
				None,
				OpaqueCall::from_encoded(call.clone()),
				false,
				Weight::zero()
			),
			Error::<Test>::NoTimepoint,
		);
		let later = Timepoint { index: 1, ..now() };
		assert_noop!(
			Multisig::as_multi(
				RuntimeOrigin::signed(2),
				2,
				vec![1, 3],
				Some(later),
				OpaqueCall::from_encoded(call),
				false,
				Weight::zero()
			),
			Error::<Test>::WrongTimepoint,
		);
	});
}

#[test]
fn multisig_2_of_3_works_with_call_storing() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(3), multi, 5));

		let call = call_transfer(6, 15);
		let call_weight = call.get_dispatch_info().weight;
		let data = call.encode();
		let hash = blake2_256(&data);
		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(1),
			2,
			vec![2, 3],
			None,
			OpaqueCall::from_encoded(data),
			true,
			Weight::zero()
		));
		assert_eq!(Balances::free_balance(6), 0);

		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(2),
			2,
			vec![1, 3],
			Some(now()),
			hash,
			call_weight
		));
		assert_eq!(Balances::free_balance(6), 15);
	});
}

#[test]
fn multisig_2_of_3_works() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(3), multi, 5));

		let call = call_transfer(6, 15);
		let call_weight = call.get_dispatch_info().weight;
		let data = call.encode();
		let hash = blake2_256(&data);
		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(1),
			2,
			vec![2, 3],
			None,
			hash,
			Weight::zero()
		));
		assert_eq!(Balances::free_balance(6), 0);

		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(2),
			2,
			vec![1, 3],
			Some(now()),
			OpaqueCall::from_encoded(data),
			false,
			call_weight
		));
		assert_eq!(Balances::free_balance(6), 15);
	});
}

#[test]
fn multisig_3_of_3_works() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 3);
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(3), multi, 5));

		let call = call_transfer(6, 15);
		let call_weight = call.get_dispatch_info().weight;
		let data = call.encode();
		let hash = blake2_256(&data);
		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(1),
			3,
			vec![2, 3],
			None,
			hash,
			Weight::zero()
		));
		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(2),
			3,
			vec![1, 3],
			Some(now()),
			hash,
			Weight::zero()
		));
		assert_eq!(Balances::free_balance(6), 0);

		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(3),
			3,
			vec![1, 2],
			Some(now()),
			OpaqueCall::from_encoded(data),
			false,
			call_weight
		));
		assert_eq!(Balances::free_balance(6), 15);
	});
}

#[test]
fn cancel_multisig_works() {
	new_test_ext().execute_with(|| {
		let call = call_transfer(6, 15).encode();
		let hash = blake2_256(&call);
		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(1),
			3,
			vec![2, 3],
			None,
			hash,
			Weight::zero()
		));
		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(2),
			3,
			vec![1, 3],
			Some(now()),
			hash,
			Weight::zero()
		));
		assert_noop!(
			Multisig::cancel_as_multi(RuntimeOrigin::signed(2), 3, vec![1, 3], now(), hash),
			Error::<Test>::NotOwner,
		);
		assert_ok!(Multisig::cancel_as_multi(RuntimeOrigin::signed(1), 3, vec![2, 3], now(), hash),);
	});
}

#[test]
fn cancel_multisig_with_call_storage_works() {
	new_test_ext().execute_with(|| {
		let call = call_transfer(6, 15).encode();
		let hash = blake2_256(&call);
		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(1),
			3,
			vec![2, 3],
			None,
			OpaqueCall::from_encoded(call),
			true,
			Weight::zero()
		));
		assert_eq!(Balances::free_balance(1), 4);
		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(2),
			3,
			vec![1, 3],
			Some(now()),
			hash,
			Weight::zero()
		));
		assert_noop!(
			Multisig::cancel_as_multi(RuntimeOrigin::signed(2), 3, vec![1, 3], now(), hash),
			Error::<Test>::NotOwner,
		);
		assert_ok!(Multisig::cancel_as_multi(RuntimeOrigin::signed(1), 3, vec![2, 3], now(), hash),);
		assert_eq!(Balances::free_balance(1), 10);
	});
}

#[test]
fn cancel_multisig_with_alt_call_storage_works() {
	new_test_ext().execute_with(|| {
		let call = call_transfer(6, 15).encode();
		let hash = blake2_256(&call);
		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(1),
			3,
			vec![2, 3],
			None,
			hash,
			Weight::zero()
		));
		assert_eq!(Balances::free_balance(1), 6);
		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(2),
			3,
			vec![1, 3],
			Some(now()),
			OpaqueCall::from_encoded(call),
			true,
			Weight::zero()
		));
		assert_eq!(Balances::free_balance(2), 8);
		assert_ok!(Multisig::cancel_as_multi(RuntimeOrigin::signed(1), 3, vec![2, 3], now(), hash));
		assert_eq!(Balances::free_balance(1), 10);
		assert_eq!(Balances::free_balance(2), 10);
	});
}

#[test]
fn multisig_2_of_3_as_multi_works() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(3), multi, 5));

		let call = call_transfer(6, 15);
		let call_weight = call.get_dispatch_info().weight;
		let data = call.encode();
		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(1),
			2,
			vec![2, 3],
			None,
			OpaqueCall::from_encoded(data.clone()),
			false,
			Weight::zero()
		));
		assert_eq!(Balances::free_balance(6), 0);

		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(2),
			2,
			vec![1, 3],
			Some(now()),
			OpaqueCall::from_encoded(data),
			false,
			call_weight
		));
		assert_eq!(Balances::free_balance(6), 15);
	});
}

#[test]
fn multisig_2_of_3_as_multi_with_many_calls_works() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(3), multi, 5));

		let call1 = call_transfer(6, 10);
		let call1_weight = call1.get_dispatch_info().weight;
		let data1 = call1.encode();
		let call2 = call_transfer(7, 5);
		let call2_weight = call2.get_dispatch_info().weight;
		let data2 = call2.encode();

		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(1),
			2,
			vec![2, 3],
			None,
			OpaqueCall::from_encoded(data1.clone()),
			false,
			Weight::zero()
		));
		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(2),
			2,
			vec![1, 3],
			None,
			OpaqueCall::from_encoded(data2.clone()),
			false,
			Weight::zero()
		));
		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(3),
			2,
			vec![1, 2],
			Some(now()),
			OpaqueCall::from_encoded(data1),
			false,
			call1_weight
		));
		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(3),
			2,
			vec![1, 2],
			Some(now()),
			OpaqueCall::from_encoded(data2),
			false,
			call2_weight
		));

		assert_eq!(Balances::free_balance(6), 10);
		assert_eq!(Balances::free_balance(7), 5);
	});
}

#[test]
fn multisig_2_of_3_cannot_reissue_same_call() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(3), multi, 5));

		let call = call_transfer(6, 10);
		let call_weight = call.get_dispatch_info().weight;
		let data = call.encode();
		let hash = blake2_256(&data);
		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(1),
			2,
			vec![2, 3],
			None,
			OpaqueCall::from_encoded(data.clone()),
			false,
			Weight::zero()
		));
		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(2),
			2,
			vec![1, 3],
			Some(now()),
			OpaqueCall::from_encoded(data.clone()),
			false,
			call_weight
		));
		assert_eq!(Balances::free_balance(multi), 5);

		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(1),
			2,
			vec![2, 3],
			None,
			OpaqueCall::from_encoded(data.clone()),
			false,
			Weight::zero()
		));
		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(3),
			2,
			vec![1, 2],
			Some(now()),
			OpaqueCall::from_encoded(data),
			false,
			call_weight
		));

		let err = DispatchError::from(BalancesError::<Test, _>::InsufficientBalance).stripped();
		System::assert_last_event(
			pallet_multisig::Event::MultisigExecuted {
				approving: 3,
				timepoint: now(),
				multisig: multi,
				call_hash: hash,
				result: Err(err),
			}
			.into(),
		);
	});
}

#[test]
fn minimum_threshold_check_works() {
	new_test_ext().execute_with(|| {
		let call = call_transfer(6, 15).encode();
		assert_noop!(
			Multisig::as_multi(
				RuntimeOrigin::signed(1),
				0,
				vec![2],
				None,
				OpaqueCall::from_encoded(call.clone()),
				false,
				Weight::zero()
			),
			Error::<Test>::MinimumThreshold,
		);
		assert_noop!(
			Multisig::as_multi(
				RuntimeOrigin::signed(1),
				1,
				vec![2],
				None,
				OpaqueCall::from_encoded(call.clone()),
				false,
				Weight::zero()
			),
			Error::<Test>::MinimumThreshold,
		);
	});
}

#[test]
fn too_many_signatories_fails() {
	new_test_ext().execute_with(|| {
		let call = call_transfer(6, 15).encode();
		assert_noop!(
			Multisig::as_multi(
				RuntimeOrigin::signed(1),
				2,
				vec![2, 3, 4],
				None,
				OpaqueCall::from_encoded(call),
				false,
				Weight::zero()
			),
			Error::<Test>::TooManySignatories,
		);
	});
}

#[test]
fn duplicate_approvals_are_ignored() {
	new_test_ext().execute_with(|| {
		let call = call_transfer(6, 15).encode();
		let hash = blake2_256(&call);
		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(1),
			2,
			vec![2, 3],
			None,
			hash,
			Weight::zero()
		));
		assert_noop!(
			Multisig::approve_as_multi(
				RuntimeOrigin::signed(1),
				2,
				vec![2, 3],
				Some(now()),
				hash,
				Weight::zero()
			),
			Error::<Test>::AlreadyApproved,
		);
		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(2),
			2,
			vec![1, 3],
			Some(now()),
			hash,
			Weight::zero()
		));
		assert_noop!(
			Multisig::approve_as_multi(
				RuntimeOrigin::signed(3),
				2,
				vec![1, 2],
				Some(now()),
				hash,
				Weight::zero()
			),
			Error::<Test>::AlreadyApproved,
		);
	});
}

#[test]
fn multisig_1_of_3_works() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 1);
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(3), multi, 5));

		let call = call_transfer(6, 15).encode();
		let hash = blake2_256(&call);
		assert_noop!(
			Multisig::approve_as_multi(
				RuntimeOrigin::signed(1),
				1,
				vec![2, 3],
				None,
				hash,
				Weight::zero()
			),
			Error::<Test>::MinimumThreshold,
		);
		assert_noop!(
			Multisig::as_multi(
				RuntimeOrigin::signed(1),
				1,
				vec![2, 3],
				None,
				OpaqueCall::from_encoded(call),
				false,
				Weight::zero()
			),
			Error::<Test>::MinimumThreshold,
		);
		let boxed_call = Box::new(call_transfer(6, 15));
		assert_ok!(Multisig::as_multi_threshold_1(
			RuntimeOrigin::signed(1),
			vec![2, 3],
			boxed_call
		));

		assert_eq!(Balances::free_balance(6), 15);
	});
}

#[test]
fn multisig_filters() {
	new_test_ext().execute_with(|| {
		let call = Box::new(RuntimeCall::System(frame_system::Call::set_code { code: vec![] }));
		assert_noop!(
			Multisig::as_multi_threshold_1(RuntimeOrigin::signed(1), vec![2], call.clone()),
			DispatchError::from(frame_system::Error::<Test>::CallFiltered),
		);
	});
}

#[test]
fn weight_check_works() {
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 2);
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(3), multi, 5));

		let call = call_transfer(6, 15);
		let data = call.encode();
		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(1),
			2,
			vec![2, 3],
			None,
			OpaqueCall::from_encoded(data.clone()),
			false,
			Weight::zero()
		));
		assert_eq!(Balances::free_balance(6), 0);

		assert_noop!(
			Multisig::as_multi(
				RuntimeOrigin::signed(2),
				2,
				vec![1, 3],
				Some(now()),
				OpaqueCall::from_encoded(data),
				false,
				Weight::zero()
			),
			Error::<Test>::MaxWeightTooLow,
		);
	});
}

#[test]
fn multisig_handles_no_preimage_after_all_approve() {
	// This test checks the situation where everyone approves a multi-sig, but no-one provides the
	// call data. In the end, any of the multisig callers can approve again with the call data and
	// the call will go through.
	new_test_ext().execute_with(|| {
		let multi = Multisig::multi_account_id(&[1, 2, 3][..], 3);
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(1), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(2), multi, 5));
		assert_ok!(Balances::transfer(RuntimeOrigin::signed(3), multi, 5));

		let call = call_transfer(6, 15);
		let call_weight = call.get_dispatch_info().weight;
		let data = call.encode();
		let hash = blake2_256(&data);
		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(1),
			3,
			vec![2, 3],
			None,
			hash,
			Weight::zero()
		));
		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(2),
			3,
			vec![1, 3],
			Some(now()),
			hash,
			Weight::zero()
		));
		assert_ok!(Multisig::approve_as_multi(
			RuntimeOrigin::signed(3),
			3,
			vec![1, 2],
			Some(now()),
			hash,
			Weight::zero()
		));
		assert_eq!(Balances::free_balance(6), 0);

		assert_ok!(Multisig::as_multi(
			RuntimeOrigin::signed(3),
			3,
			vec![1, 2],
			Some(now()),
			OpaqueCall::from_encoded(data),
			false,
			call_weight
		));
		assert_eq!(Balances::free_balance(6), 15);
	});
}
