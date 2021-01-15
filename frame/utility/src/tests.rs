// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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
	assert_ok, assert_noop, impl_outer_origin, parameter_types, impl_outer_dispatch, impl_outer_event,
	assert_err_ignore_postinfo,
	weights::{Weight, Pays},
	dispatch::{DispatchError, DispatchErrorWithPostInfo, Dispatchable},
	traits::Filter,
	storage,
};
use sp_core::H256;
use sp_runtime::{traits::{BlakeTwo256, IdentityLookup}, testing::Header};
use crate as utility;

// example module to test behaviors.
pub mod example {
	use super::*;
	use frame_support::dispatch::WithPostDispatchInfo;
	pub trait Config: frame_system::Config { }

	decl_module! {
		pub struct Module<T: Config> for enum Call where origin: <T as frame_system::Config>::Origin {
			#[weight = *weight]
			fn noop(_origin, weight: Weight) { }

			#[weight = *start_weight]
			fn foobar(
				origin,
				err: bool,
				start_weight: Weight,
				end_weight: Option<Weight>,
			) -> DispatchResultWithPostInfo {
				let _ = ensure_signed(origin)?;
				if err {
					let error: DispatchError = "The cake is a lie.".into();
					if let Some(weight) = end_weight {
						Err(error.with_weight(weight))
					} else {
						Err(error)?
					}
				} else {
					Ok(end_weight.into())
				}
			}
		}
	}
}

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
		example::Example,
	}
}

// For testing the pallet, we construct most of a mock runtime. This means
// first constructing a configuration type (`Test`) which `impl`s each of the
// configuration traits of pallets we want to use.
#[derive(Clone, Eq, PartialEq)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(Weight::max_value());
}
impl frame_system::Config for Test {
	type BaseCallFilter = TestBaseCallFilter;
	type BlockWeights = BlockWeights;
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
	type Event = TestEvent;
	type BlockHashCount = BlockHashCount;
	type Version = ();
	type PalletInfo = ();
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

impl example::Config for Test {}

pub struct TestBaseCallFilter;
impl Filter<Call> for TestBaseCallFilter {
	fn filter(c: &Call) -> bool {
		match *c {
			Call::Balances(_) => true,
			Call::Utility(_) => true,
			// For benchmarking, this acts as a noop call
			Call::System(frame_system::Call::remark(..)) => true,
			// For tests
			Call::Example(_) => true,
			_ => false,
		}
	}
}
impl Config for Test {
	type Event = TestEvent;
	type Call = Call;
	type WeightInfo = ();
}
type System = frame_system::Module<Test>;
type Balances = pallet_balances::Module<Test>;
type Example = example::Module<Test>;
type Utility = Module<Test>;

type ExampleCall = example::Call<Test>;
type UtilityCall = crate::Call<Test>;

use frame_system::Call as SystemCall;
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
		assert_err_ignore_postinfo!(Utility::as_derivative(
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
fn as_derivative_handles_weight_refund() {
	new_test_ext().execute_with(|| {
		let start_weight = 100;
		let end_weight = 75;
		let diff = start_weight - end_weight;

		// Full weight when ok
		let inner_call = Call::Example(ExampleCall::foobar(false, start_weight, None));
		let call = Call::Utility(UtilityCall::as_derivative(0, Box::new(inner_call)));
		let info = call.get_dispatch_info();
		let result = call.dispatch(Origin::signed(1));
		assert_ok!(result);
		assert_eq!(extract_actual_weight(&result, &info), info.weight);

		// Refund weight when ok
		let inner_call = Call::Example(ExampleCall::foobar(false, start_weight, Some(end_weight)));
		let call = Call::Utility(UtilityCall::as_derivative(0, Box::new(inner_call)));
		let info = call.get_dispatch_info();
		let result = call.dispatch(Origin::signed(1));
		assert_ok!(result);
		// Diff is refunded
		assert_eq!(extract_actual_weight(&result, &info), info.weight - diff);

		// Full weight when err
		let inner_call = Call::Example(ExampleCall::foobar(true, start_weight, None));
		let call = Call::Utility(UtilityCall::as_derivative(0, Box::new(inner_call)));
		let info = call.get_dispatch_info();
		let result = call.dispatch(Origin::signed(1));
		assert_noop!(
			result,
			DispatchErrorWithPostInfo {
				post_info: PostDispatchInfo {
					// No weight is refunded
					actual_weight: Some(info.weight),
					pays_fee: Pays::Yes,
				},
				error: DispatchError::Other("The cake is a lie."),
			}
		);

		// Refund weight when err
		let inner_call = Call::Example(ExampleCall::foobar(true, start_weight, Some(end_weight)));
		let call = Call::Utility(UtilityCall::as_derivative(0, Box::new(inner_call)));
		let info = call.get_dispatch_info();
		let result = call.dispatch(Origin::signed(1));
		assert_noop!(
			result,
			DispatchErrorWithPostInfo {
				post_info: PostDispatchInfo {
					// Diff is refunded
					actual_weight: Some(info.weight - diff),
					pays_fee: Pays::Yes,
				},
				error: DispatchError::Other("The cake is a lie."),
			}
		);
	});
}

#[test]
fn as_derivative_filters() {
	new_test_ext().execute_with(|| {
		assert_err_ignore_postinfo!(Utility::as_derivative(
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

#[test]
fn batch_weight_calculation_doesnt_overflow() {
	use sp_runtime::Perbill;
	new_test_ext().execute_with(|| {
		let big_call = Call::System(SystemCall::fill_block(Perbill::from_percent(50)));
		assert_eq!(big_call.get_dispatch_info().weight, Weight::max_value() / 2);

		// 3 * 50% saturates to 100%
		let batch_call = Call::Utility(crate::Call::batch(vec![
			big_call.clone(),
			big_call.clone(),
			big_call.clone(),
		]));

		assert_eq!(batch_call.get_dispatch_info().weight, Weight::max_value());
	});
}

#[test]
fn batch_handles_weight_refund() {
	new_test_ext().execute_with(|| {
		let start_weight = 100;
		let end_weight = 75;
		let diff = start_weight - end_weight;
		let batch_len: Weight = 4;

		// Full weight when ok
		let inner_call = Call::Example(ExampleCall::foobar(false, start_weight, None));
		let batch_calls = vec![inner_call; batch_len as usize];
		let call = Call::Utility(UtilityCall::batch(batch_calls));
		let info = call.get_dispatch_info();
		let result = call.dispatch(Origin::signed(1));
		assert_ok!(result);
		assert_eq!(extract_actual_weight(&result, &info), info.weight);

		// Refund weight when ok
		let inner_call = Call::Example(ExampleCall::foobar(false, start_weight, Some(end_weight)));
		let batch_calls = vec![inner_call; batch_len as usize];
		let call = Call::Utility(UtilityCall::batch(batch_calls));
		let info = call.get_dispatch_info();
		let result = call.dispatch(Origin::signed(1));
		assert_ok!(result);
		// Diff is refunded
		assert_eq!(extract_actual_weight(&result, &info), info.weight - diff * batch_len);

		// Full weight when err
		let good_call = Call::Example(ExampleCall::foobar(false, start_weight, None));
		let bad_call = Call::Example(ExampleCall::foobar(true, start_weight, None));
		let batch_calls = vec![good_call, bad_call];
		let call = Call::Utility(UtilityCall::batch(batch_calls));
		let info = call.get_dispatch_info();
		let result = call.dispatch(Origin::signed(1));
		assert_ok!(result);
		expect_event(Event::BatchInterrupted(1, DispatchError::Other("")));
		// No weight is refunded
		assert_eq!(extract_actual_weight(&result, &info), info.weight);

		// Refund weight when err
		let good_call = Call::Example(ExampleCall::foobar(false, start_weight, Some(end_weight)));
		let bad_call = Call::Example(ExampleCall::foobar(true, start_weight, Some(end_weight)));
		let batch_calls = vec![good_call, bad_call];
		let batch_len = batch_calls.len() as Weight;
		let call = Call::Utility(UtilityCall::batch(batch_calls));
		let info = call.get_dispatch_info();
		let result = call.dispatch(Origin::signed(1));
		assert_ok!(result);
		expect_event(Event::BatchInterrupted(1, DispatchError::Other("")));
		assert_eq!(extract_actual_weight(&result, &info), info.weight - diff * batch_len);

		// Partial batch completion
		let good_call = Call::Example(ExampleCall::foobar(false, start_weight, Some(end_weight)));
		let bad_call = Call::Example(ExampleCall::foobar(true, start_weight, Some(end_weight)));
		let batch_calls = vec![good_call, bad_call.clone(), bad_call];
		let call = Call::Utility(UtilityCall::batch(batch_calls));
		let info = call.get_dispatch_info();
		let result = call.dispatch(Origin::signed(1));
		assert_ok!(result);
		expect_event(Event::BatchInterrupted(1, DispatchError::Other("")));
		assert_eq!(
			extract_actual_weight(&result, &info),
			// Real weight is 2 calls at end_weight
			<Test as Config>::WeightInfo::batch(2) + end_weight * 2,
		);
	});
}

#[test]
fn batch_all_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Balances::free_balance(1), 10);
		assert_eq!(Balances::free_balance(2), 10);
		assert_ok!(
			Utility::batch_all(Origin::signed(1), vec![
				Call::Balances(BalancesCall::transfer(2, 5)),
				Call::Balances(BalancesCall::transfer(2, 5))
			]),
		);
		assert_eq!(Balances::free_balance(1), 0);
		assert_eq!(Balances::free_balance(2), 20);
	});
}

#[test]
fn batch_all_revert() {
	new_test_ext().execute_with(|| {
		let call = Call::Balances(BalancesCall::transfer(2, 5));
		let info = call.get_dispatch_info();

		assert_eq!(Balances::free_balance(1), 10);
		assert_eq!(Balances::free_balance(2), 10);
		assert_noop!(
			Utility::batch_all(Origin::signed(1), vec![
				Call::Balances(BalancesCall::transfer(2, 5)),
				Call::Balances(BalancesCall::transfer(2, 10)),
				Call::Balances(BalancesCall::transfer(2, 5)),
			]),
			DispatchErrorWithPostInfo {
				post_info: PostDispatchInfo {
					actual_weight: Some(<Test as Config>::WeightInfo::batch_all(2) + info.weight * 2),
					pays_fee: Pays::Yes
				},
				error: pallet_balances::Error::<Test, _>::InsufficientBalance.into()
			}
		);
		assert_eq!(Balances::free_balance(1), 10);
		assert_eq!(Balances::free_balance(2), 10);
	});
}

#[test]
fn batch_all_handles_weight_refund() {
	new_test_ext().execute_with(|| {
		let start_weight = 100;
		let end_weight = 75;
		let diff = start_weight - end_weight;
		let batch_len: Weight = 4;

		// Full weight when ok
		let inner_call = Call::Example(ExampleCall::foobar(false, start_weight, None));
		let batch_calls = vec![inner_call; batch_len as usize];
		let call = Call::Utility(UtilityCall::batch_all(batch_calls));
		let info = call.get_dispatch_info();
		let result = call.dispatch(Origin::signed(1));
		assert_ok!(result);
		assert_eq!(extract_actual_weight(&result, &info), info.weight);

		// Refund weight when ok
		let inner_call = Call::Example(ExampleCall::foobar(false, start_weight, Some(end_weight)));
		let batch_calls = vec![inner_call; batch_len as usize];
		let call = Call::Utility(UtilityCall::batch_all(batch_calls));
		let info = call.get_dispatch_info();
		let result = call.dispatch(Origin::signed(1));
		assert_ok!(result);
		// Diff is refunded
		assert_eq!(extract_actual_weight(&result, &info), info.weight - diff * batch_len);

		// Full weight when err
		let good_call = Call::Example(ExampleCall::foobar(false, start_weight, None));
		let bad_call = Call::Example(ExampleCall::foobar(true, start_weight, None));
		let batch_calls = vec![good_call, bad_call];
		let call = Call::Utility(UtilityCall::batch_all(batch_calls));
		let info = call.get_dispatch_info();
		let result = call.dispatch(Origin::signed(1));
		assert_err_ignore_postinfo!(result, "The cake is a lie.");
		// No weight is refunded
		assert_eq!(extract_actual_weight(&result, &info), info.weight);

		// Refund weight when err
		let good_call = Call::Example(ExampleCall::foobar(false, start_weight, Some(end_weight)));
		let bad_call = Call::Example(ExampleCall::foobar(true, start_weight, Some(end_weight)));
		let batch_calls = vec![good_call, bad_call];
		let batch_len = batch_calls.len() as Weight;
		let call = Call::Utility(UtilityCall::batch_all(batch_calls));
		let info = call.get_dispatch_info();
		let result = call.dispatch(Origin::signed(1));
		assert_err_ignore_postinfo!(result, "The cake is a lie.");
		assert_eq!(extract_actual_weight(&result, &info), info.weight - diff * batch_len);

		// Partial batch completion
		let good_call = Call::Example(ExampleCall::foobar(false, start_weight, Some(end_weight)));
		let bad_call = Call::Example(ExampleCall::foobar(true, start_weight, Some(end_weight)));
		let batch_calls = vec![good_call, bad_call.clone(), bad_call];
		let call = Call::Utility(UtilityCall::batch_all(batch_calls));
		let info = call.get_dispatch_info();
		let result = call.dispatch(Origin::signed(1));
		assert_err_ignore_postinfo!(result, "The cake is a lie.");
		assert_eq!(
			extract_actual_weight(&result, &info),
			// Real weight is 2 calls at end_weight
			<Test as Config>::WeightInfo::batch_all(2) + end_weight * 2,
		);
	});
}
