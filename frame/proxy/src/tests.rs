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

// Tests for Proxy Pallet

#![cfg(test)]

use super::*;

use frame_support::{
	assert_ok, assert_noop, impl_outer_origin, parameter_types, impl_outer_dispatch,
	weights::Weight, impl_outer_event, RuntimeDebug
};
use codec::{Encode, Decode};
use sp_core::H256;
use sp_runtime::{Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header};
use crate as proxy;

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}
impl_outer_event! {
	pub enum TestEvent for Test {
		system<T>,
		pallet_balances<T>,
		proxy,
	}
}
impl_outer_dispatch! {
	pub enum Call for Test where origin: Origin {
		frame_system::System,
		pallet_balances::Balances,
		proxy::Proxy,
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
	pub const ProxyDepositBase: u64 = 1;
	pub const ProxyDepositFactor: u64 = 1;
	pub const MaxProxies: u16 = 3;
}
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Encode, Decode, RuntimeDebug)]
pub enum ProxyType {
	Any,
	JustTransfer,
}
impl Default for ProxyType { fn default() -> Self { Self::Any } }
impl InstanceFilter<Call> for ProxyType {
	fn filter(&self, c: &Call) -> bool {
		match self {
			ProxyType::Any => true,
			ProxyType::JustTransfer => match c {
				Call::Balances(pallet_balances::Call::transfer(..)) => true,
				_ => false,
			}
		}
	}
}
pub struct TestIsCallable;
impl Filter<Call> for TestIsCallable {
	fn filter(c: &Call) -> bool {
		match *c {
			Call::Balances(_) => true,
			_ => false,
		}
	}
}
impl Trait for Test {
	type Event = TestEvent;
	type Call = Call;
	type Currency = Balances;
	type IsCallable = TestIsCallable;
	type ProxyType = ProxyType;
	type ProxyDepositBase = ProxyDepositBase;
	type ProxyDepositFactor = ProxyDepositFactor;
	type MaxProxies = MaxProxies;
}

type System = frame_system::Module<Test>;
type Balances = pallet_balances::Module<Test>;
type Proxy = Module<Test>;

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
	system::Module::<Test>::events().pop().map(|e| e.event).expect("Event expected")
}

fn expect_event<E: Into<TestEvent>>(e: E) {
	assert_eq!(last_event(), e.into());
}

#[test]
fn add_remove_proxies_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Proxy::add_proxy(Origin::signed(1), 2, ProxyType::Any));
		assert_noop!(Proxy::add_proxy(Origin::signed(1), 2, ProxyType::Any), Error::<Test>::Duplicate);
		assert_eq!(Balances::reserved_balance(1), 2);
		assert_ok!(Proxy::add_proxy(Origin::signed(1), 2, ProxyType::JustTransfer));
		assert_eq!(Balances::reserved_balance(1), 3);
		assert_ok!(Proxy::add_proxy(Origin::signed(1), 3, ProxyType::Any));
		assert_eq!(Balances::reserved_balance(1), 4);
		assert_noop!(Proxy::add_proxy(Origin::signed(1), 4, ProxyType::Any), Error::<Test>::TooMany);
		assert_noop!(Proxy::remove_proxy(Origin::signed(1), 3, ProxyType::JustTransfer), Error::<Test>::NotFound);
		assert_ok!(Proxy::remove_proxy(Origin::signed(1), 3, ProxyType::Any));
		assert_eq!(Balances::reserved_balance(1), 3);
		assert_ok!(Proxy::remove_proxy(Origin::signed(1), 2, ProxyType::Any));
		assert_eq!(Balances::reserved_balance(1), 2);
		assert_ok!(Proxy::remove_proxy(Origin::signed(1), 2, ProxyType::JustTransfer));
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn cannot_add_proxy_without_balance() {
	new_test_ext().execute_with(|| {
		assert_ok!(Proxy::add_proxy(Origin::signed(5), 3, ProxyType::Any));
		assert_eq!(Balances::reserved_balance(5), 2);
		assert_noop!(
			Proxy::add_proxy(Origin::signed(5), 4, ProxyType::Any),
			BalancesError::<Test, _>::InsufficientBalance
		);
	});
}

#[test]
fn proxying_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Proxy::add_proxy(Origin::signed(1), 2, ProxyType::JustTransfer));
		assert_ok!(Proxy::add_proxy(Origin::signed(1), 3, ProxyType::Any));

		let call = Box::new(Call::Balances(BalancesCall::transfer(6, 1)));
		assert_noop!(Proxy::proxy(Origin::signed(4), 1, None, call.clone()), Error::<Test>::NotProxy);
		assert_noop!(Proxy::proxy(Origin::signed(2), 1, Some(ProxyType::Any), call.clone()), Error::<Test>::NotProxy);
		assert_ok!(Proxy::proxy(Origin::signed(2), 1, None, call.clone()));
		expect_event(Event::ProxyExecuted(Ok(())));
		assert_eq!(Balances::free_balance(6), 1);

		let call = Box::new(Call::System(SystemCall::remark(vec![])));
		assert_noop!(Proxy::proxy(Origin::signed(3), 1, None, call.clone()), Error::<Test>::Uncallable);

		let call = Box::new(Call::Balances(BalancesCall::transfer_keep_alive(6, 1)));
		assert_noop!(Proxy::proxy(Origin::signed(2), 1, None, call.clone()), Error::<Test>::Unproxyable);
		assert_ok!(Proxy::proxy(Origin::signed(3), 1, None, call.clone()));
		expect_event(Event::ProxyExecuted(Ok(())));
		assert_eq!(Balances::free_balance(6), 2);
	});
}
