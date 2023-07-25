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

// Tests for Proxy Pallet

#![cfg(test)]

use super::*;

use crate as proxy;
use codec::{Decode, Encode};
use frame_support::{
	assert_noop, assert_ok,
	dispatch::DispatchError,
	traits::{ConstU32, ConstU64, Contains},
	RuntimeDebug,
};
use sp_core::H256;
use sp_runtime::{
	traits::{BlakeTwo256, IdentityLookup},
	BuildStorage,
};

type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test
	{
		System: frame_system::{Pallet, Call, Config<T>, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Proxy: proxy::{Pallet, Call, Storage, Event<T>},
		Utility: pallet_utility::{Pallet, Call, Event},
	}
);

impl frame_system::Config for Test {
	type BaseCallFilter = BaseFilter;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Nonce = u64;
	type Hash = H256;
	type RuntimeCall = RuntimeCall;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Block = Block;
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
	type FreezeIdentifier = ();
	type MaxFreezes = ();
	type RuntimeHoldReason = ();
	type MaxHolds = ();
}
impl pallet_utility::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type RuntimeCall = RuntimeCall;
	type PalletsOrigin = OriginCaller;
	type WeightInfo = ();
}

#[derive(
	Copy,
	Clone,
	Eq,
	PartialEq,
	Ord,
	PartialOrd,
	Encode,
	Decode,
	RuntimeDebug,
	MaxEncodedLen,
	scale_info::TypeInfo,
)]
pub enum ProxyType {
	Any,
	JustTransfer,
	JustUtility,
}
impl Default for ProxyType {
	fn default() -> Self {
		Self::Any
	}
}
impl InstanceFilter<RuntimeCall> for ProxyType {
	fn filter(&self, c: &RuntimeCall) -> bool {
		match self {
			ProxyType::Any => true,
			ProxyType::JustTransfer => {
				matches!(
					c,
					RuntimeCall::Balances(pallet_balances::Call::transfer_allow_death { .. })
				)
			},
			ProxyType::JustUtility => matches!(c, RuntimeCall::Utility { .. }),
		}
	}
	fn is_superset(&self, o: &Self) -> bool {
		self == &ProxyType::Any || self == o
	}
}
pub struct BaseFilter;
impl Contains<RuntimeCall> for BaseFilter {
	fn contains(c: &RuntimeCall) -> bool {
		match *c {
			// Remark is used as a no-op call in the benchmarking
			RuntimeCall::System(SystemCall::remark { .. }) => true,
			RuntimeCall::System(_) => false,
			_ => true,
		}
	}
}
impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type RuntimeCall = RuntimeCall;
	type Currency = Balances;
	type ProxyType = ProxyType;
	type ProxyDepositBase = ConstU64<1>;
	type ProxyDepositFactor = ConstU64<1>;
	type MaxProxies = ConstU32<4>;
	type WeightInfo = ();
	type CallHasher = BlakeTwo256;
	type MaxPending = ConstU32<2>;
	type AnnouncementDepositBase = ConstU64<1>;
	type AnnouncementDepositFactor = ConstU64<1>;
}

use super::{Call as ProxyCall, Event as ProxyEvent};
use frame_system::Call as SystemCall;
use pallet_balances::{Call as BalancesCall, Event as BalancesEvent};
use pallet_utility::{Call as UtilityCall, Event as UtilityEvent};

type SystemError = frame_system::Error<Test>;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::<Test>::default().build_storage().unwrap();
	pallet_balances::GenesisConfig::<Test> {
		balances: vec![(1, 10), (2, 10), (3, 10), (4, 10), (5, 3)],
	}
	.assimilate_storage(&mut t)
	.unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

fn last_events(n: usize) -> Vec<RuntimeEvent> {
	system::Pallet::<Test>::events()
		.into_iter()
		.rev()
		.take(n)
		.rev()
		.map(|e| e.event)
		.collect()
}

fn expect_events(e: Vec<RuntimeEvent>) {
	assert_eq!(last_events(e.len()), e);
}

fn call_transfer(dest: u64, value: u64) -> RuntimeCall {
	RuntimeCall::Balances(BalancesCall::transfer_allow_death { dest, value })
}

#[test]
fn announcement_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 3, ProxyType::Any, 1));
		System::assert_last_event(
			ProxyEvent::ProxyAdded {
				delegator: 1,
				delegatee: 3,
				proxy_type: ProxyType::Any,
				delay: 1,
			}
			.into(),
		);
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(2), 3, ProxyType::Any, 1));
		assert_eq!(Balances::reserved_balance(3), 0);

		assert_ok!(Proxy::announce(RuntimeOrigin::signed(3), 1, [1; 32].into()));
		let announcements = Announcements::<Test>::get(3);
		assert_eq!(
			announcements.0,
			vec![Announcement { real: 1, call_hash: [1; 32].into(), height: 1 }]
		);
		assert_eq!(Balances::reserved_balance(3), announcements.1);

		assert_ok!(Proxy::announce(RuntimeOrigin::signed(3), 2, [2; 32].into()));
		let announcements = Announcements::<Test>::get(3);
		assert_eq!(
			announcements.0,
			vec![
				Announcement { real: 1, call_hash: [1; 32].into(), height: 1 },
				Announcement { real: 2, call_hash: [2; 32].into(), height: 1 },
			]
		);
		assert_eq!(Balances::reserved_balance(3), announcements.1);

		assert_noop!(
			Proxy::announce(RuntimeOrigin::signed(3), 2, [3; 32].into()),
			Error::<Test>::TooMany
		);
	});
}

#[test]
fn remove_announcement_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 3, ProxyType::Any, 1));
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(2), 3, ProxyType::Any, 1));
		assert_ok!(Proxy::announce(RuntimeOrigin::signed(3), 1, [1; 32].into()));
		assert_ok!(Proxy::announce(RuntimeOrigin::signed(3), 2, [2; 32].into()));
		let e = Error::<Test>::NotFound;
		assert_noop!(Proxy::remove_announcement(RuntimeOrigin::signed(3), 1, [0; 32].into()), e);
		assert_ok!(Proxy::remove_announcement(RuntimeOrigin::signed(3), 1, [1; 32].into()));
		let announcements = Announcements::<Test>::get(3);
		assert_eq!(
			announcements.0,
			vec![Announcement { real: 2, call_hash: [2; 32].into(), height: 1 }]
		);
		assert_eq!(Balances::reserved_balance(3), announcements.1);
	});
}

#[test]
fn reject_announcement_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 3, ProxyType::Any, 1));
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(2), 3, ProxyType::Any, 1));
		assert_ok!(Proxy::announce(RuntimeOrigin::signed(3), 1, [1; 32].into()));
		assert_ok!(Proxy::announce(RuntimeOrigin::signed(3), 2, [2; 32].into()));
		let e = Error::<Test>::NotFound;
		assert_noop!(Proxy::reject_announcement(RuntimeOrigin::signed(1), 3, [0; 32].into()), e);
		let e = Error::<Test>::NotFound;
		assert_noop!(Proxy::reject_announcement(RuntimeOrigin::signed(4), 3, [1; 32].into()), e);
		assert_ok!(Proxy::reject_announcement(RuntimeOrigin::signed(1), 3, [1; 32].into()));
		let announcements = Announcements::<Test>::get(3);
		assert_eq!(
			announcements.0,
			vec![Announcement { real: 2, call_hash: [2; 32].into(), height: 1 }]
		);
		assert_eq!(Balances::reserved_balance(3), announcements.1);
	});
}

#[test]
fn announcer_must_be_proxy() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			Proxy::announce(RuntimeOrigin::signed(2), 1, H256::zero()),
			Error::<Test>::NotProxy
		);
	});
}

#[test]
fn calling_proxy_doesnt_remove_announcement() {
	new_test_ext().execute_with(|| {
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 2, ProxyType::Any, 0));

		let call = Box::new(call_transfer(6, 1));
		let call_hash = BlakeTwo256::hash_of(&call);

		assert_ok!(Proxy::announce(RuntimeOrigin::signed(2), 1, call_hash));
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(2), 1, None, call));

		// The announcement is not removed by calling proxy.
		let announcements = Announcements::<Test>::get(2);
		assert_eq!(announcements.0, vec![Announcement { real: 1, call_hash, height: 1 }]);
	});
}

#[test]
fn delayed_requires_pre_announcement() {
	new_test_ext().execute_with(|| {
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 2, ProxyType::Any, 1));
		let call = Box::new(call_transfer(6, 1));
		let e = Error::<Test>::Unannounced;
		assert_noop!(Proxy::proxy(RuntimeOrigin::signed(2), 1, None, call.clone()), e);
		let e = Error::<Test>::Unannounced;
		assert_noop!(Proxy::proxy_announced(RuntimeOrigin::signed(0), 2, 1, None, call.clone()), e);
		let call_hash = BlakeTwo256::hash_of(&call);
		assert_ok!(Proxy::announce(RuntimeOrigin::signed(2), 1, call_hash));
		system::Pallet::<Test>::set_block_number(2);
		assert_ok!(Proxy::proxy_announced(RuntimeOrigin::signed(0), 2, 1, None, call.clone()));
	});
}

#[test]
fn proxy_announced_removes_announcement_and_returns_deposit() {
	new_test_ext().execute_with(|| {
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 3, ProxyType::Any, 1));
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(2), 3, ProxyType::Any, 1));
		let call = Box::new(call_transfer(6, 1));
		let call_hash = BlakeTwo256::hash_of(&call);
		assert_ok!(Proxy::announce(RuntimeOrigin::signed(3), 1, call_hash));
		assert_ok!(Proxy::announce(RuntimeOrigin::signed(3), 2, call_hash));
		// Too early to execute announced call
		let e = Error::<Test>::Unannounced;
		assert_noop!(Proxy::proxy_announced(RuntimeOrigin::signed(0), 3, 1, None, call.clone()), e);

		system::Pallet::<Test>::set_block_number(2);
		assert_ok!(Proxy::proxy_announced(RuntimeOrigin::signed(0), 3, 1, None, call.clone()));
		let announcements = Announcements::<Test>::get(3);
		assert_eq!(announcements.0, vec![Announcement { real: 2, call_hash, height: 1 }]);
		assert_eq!(Balances::reserved_balance(3), announcements.1);
	});
}

#[test]
fn filtering_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 1000);
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 2, ProxyType::Any, 0));
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 3, ProxyType::JustTransfer, 0));
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 4, ProxyType::JustUtility, 0));

		let call = Box::new(call_transfer(6, 1));
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(2), 1, None, call.clone()));
		System::assert_last_event(ProxyEvent::ProxyExecuted { result: Ok(()) }.into());
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(3), 1, None, call.clone()));
		System::assert_last_event(ProxyEvent::ProxyExecuted { result: Ok(()) }.into());
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(4), 1, None, call.clone()));
		System::assert_last_event(
			ProxyEvent::ProxyExecuted { result: Err(SystemError::CallFiltered.into()) }.into(),
		);

		let derivative_id = Utility::derivative_account_id(1, 0);
		Balances::make_free_balance_be(&derivative_id, 1000);
		let inner = Box::new(call_transfer(6, 1));

		let call = Box::new(RuntimeCall::Utility(UtilityCall::as_derivative {
			index: 0,
			call: inner.clone(),
		}));
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(2), 1, None, call.clone()));
		System::assert_last_event(ProxyEvent::ProxyExecuted { result: Ok(()) }.into());
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(3), 1, None, call.clone()));
		System::assert_last_event(
			ProxyEvent::ProxyExecuted { result: Err(SystemError::CallFiltered.into()) }.into(),
		);
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(4), 1, None, call.clone()));
		System::assert_last_event(
			ProxyEvent::ProxyExecuted { result: Err(SystemError::CallFiltered.into()) }.into(),
		);

		let call = Box::new(RuntimeCall::Utility(UtilityCall::batch { calls: vec![*inner] }));
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(2), 1, None, call.clone()));
		expect_events(vec![
			UtilityEvent::BatchCompleted.into(),
			ProxyEvent::ProxyExecuted { result: Ok(()) }.into(),
		]);
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(3), 1, None, call.clone()));
		System::assert_last_event(
			ProxyEvent::ProxyExecuted { result: Err(SystemError::CallFiltered.into()) }.into(),
		);
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(4), 1, None, call.clone()));
		expect_events(vec![
			UtilityEvent::BatchInterrupted { index: 0, error: SystemError::CallFiltered.into() }
				.into(),
			ProxyEvent::ProxyExecuted { result: Ok(()) }.into(),
		]);

		let inner = Box::new(RuntimeCall::Proxy(ProxyCall::new_call_variant_add_proxy(
			5,
			ProxyType::Any,
			0,
		)));
		let call = Box::new(RuntimeCall::Utility(UtilityCall::batch { calls: vec![*inner] }));
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(2), 1, None, call.clone()));
		expect_events(vec![
			UtilityEvent::BatchCompleted.into(),
			ProxyEvent::ProxyExecuted { result: Ok(()) }.into(),
		]);
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(3), 1, None, call.clone()));
		System::assert_last_event(
			ProxyEvent::ProxyExecuted { result: Err(SystemError::CallFiltered.into()) }.into(),
		);
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(4), 1, None, call.clone()));
		expect_events(vec![
			UtilityEvent::BatchInterrupted { index: 0, error: SystemError::CallFiltered.into() }
				.into(),
			ProxyEvent::ProxyExecuted { result: Ok(()) }.into(),
		]);

		let call = Box::new(RuntimeCall::Proxy(ProxyCall::remove_proxies {}));
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(3), 1, None, call.clone()));
		System::assert_last_event(
			ProxyEvent::ProxyExecuted { result: Err(SystemError::CallFiltered.into()) }.into(),
		);
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(4), 1, None, call.clone()));
		System::assert_last_event(
			ProxyEvent::ProxyExecuted { result: Err(SystemError::CallFiltered.into()) }.into(),
		);
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(2), 1, None, call.clone()));
		expect_events(vec![
			BalancesEvent::<Test>::Unreserved { who: 1, amount: 5 }.into(),
			ProxyEvent::ProxyExecuted { result: Ok(()) }.into(),
		]);
	});
}

#[test]
fn add_remove_proxies_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 2, ProxyType::Any, 0));
		assert_noop!(
			Proxy::add_proxy(RuntimeOrigin::signed(1), 2, ProxyType::Any, 0),
			Error::<Test>::Duplicate
		);
		assert_eq!(Balances::reserved_balance(1), 2);
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 2, ProxyType::JustTransfer, 0));
		assert_eq!(Balances::reserved_balance(1), 3);
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 3, ProxyType::Any, 0));
		assert_eq!(Balances::reserved_balance(1), 4);
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 4, ProxyType::JustUtility, 0));
		assert_eq!(Balances::reserved_balance(1), 5);
		assert_noop!(
			Proxy::add_proxy(RuntimeOrigin::signed(1), 4, ProxyType::Any, 0),
			Error::<Test>::TooMany
		);
		assert_noop!(
			Proxy::remove_proxy(RuntimeOrigin::signed(1), 3, ProxyType::JustTransfer, 0),
			Error::<Test>::NotFound
		);
		assert_ok!(Proxy::remove_proxy(RuntimeOrigin::signed(1), 4, ProxyType::JustUtility, 0));
		System::assert_last_event(
			ProxyEvent::ProxyRemoved {
				delegator: 1,
				delegatee: 4,
				proxy_type: ProxyType::JustUtility,
				delay: 0,
			}
			.into(),
		);
		assert_eq!(Balances::reserved_balance(1), 4);
		assert_ok!(Proxy::remove_proxy(RuntimeOrigin::signed(1), 3, ProxyType::Any, 0));
		assert_eq!(Balances::reserved_balance(1), 3);
		System::assert_last_event(
			ProxyEvent::ProxyRemoved {
				delegator: 1,
				delegatee: 3,
				proxy_type: ProxyType::Any,
				delay: 0,
			}
			.into(),
		);
		assert_ok!(Proxy::remove_proxy(RuntimeOrigin::signed(1), 2, ProxyType::Any, 0));
		assert_eq!(Balances::reserved_balance(1), 2);
		System::assert_last_event(
			ProxyEvent::ProxyRemoved {
				delegator: 1,
				delegatee: 2,
				proxy_type: ProxyType::Any,
				delay: 0,
			}
			.into(),
		);
		assert_ok!(Proxy::remove_proxy(RuntimeOrigin::signed(1), 2, ProxyType::JustTransfer, 0));
		assert_eq!(Balances::reserved_balance(1), 0);
		System::assert_last_event(
			ProxyEvent::ProxyRemoved {
				delegator: 1,
				delegatee: 2,
				proxy_type: ProxyType::JustTransfer,
				delay: 0,
			}
			.into(),
		);
		assert_noop!(
			Proxy::add_proxy(RuntimeOrigin::signed(1), 1, ProxyType::Any, 0),
			Error::<Test>::NoSelfProxy
		);
	});
}

#[test]
fn cannot_add_proxy_without_balance() {
	new_test_ext().execute_with(|| {
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(5), 3, ProxyType::Any, 0));
		assert_eq!(Balances::reserved_balance(5), 2);
		assert_noop!(
			Proxy::add_proxy(RuntimeOrigin::signed(5), 4, ProxyType::Any, 0),
			DispatchError::ConsumerRemaining,
		);
	});
}

#[test]
fn proxying_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 2, ProxyType::JustTransfer, 0));
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 3, ProxyType::Any, 0));

		let call = Box::new(call_transfer(6, 1));
		assert_noop!(
			Proxy::proxy(RuntimeOrigin::signed(4), 1, None, call.clone()),
			Error::<Test>::NotProxy
		);
		assert_noop!(
			Proxy::proxy(RuntimeOrigin::signed(2), 1, Some(ProxyType::Any), call.clone()),
			Error::<Test>::NotProxy
		);
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(2), 1, None, call.clone()));
		System::assert_last_event(ProxyEvent::ProxyExecuted { result: Ok(()) }.into());
		assert_eq!(Balances::free_balance(6), 1);

		let call = Box::new(RuntimeCall::System(SystemCall::set_code { code: vec![] }));
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(3), 1, None, call.clone()));
		System::assert_last_event(
			ProxyEvent::ProxyExecuted { result: Err(SystemError::CallFiltered.into()) }.into(),
		);

		let call = Box::new(RuntimeCall::Balances(BalancesCall::transfer_keep_alive {
			dest: 6,
			value: 1,
		}));
		assert_ok!(RuntimeCall::Proxy(super::Call::new_call_variant_proxy(1, None, call.clone()))
			.dispatch(RuntimeOrigin::signed(2)));
		System::assert_last_event(
			ProxyEvent::ProxyExecuted { result: Err(SystemError::CallFiltered.into()) }.into(),
		);
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(3), 1, None, call.clone()));
		System::assert_last_event(ProxyEvent::ProxyExecuted { result: Ok(()) }.into());
		assert_eq!(Balances::free_balance(6), 2);
	});
}

#[test]
fn pure_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&1, 11); // An extra one for the ED.
		assert_ok!(Proxy::create_pure(RuntimeOrigin::signed(1), ProxyType::Any, 0, 0));
		let anon = Proxy::pure_account(&1, &ProxyType::Any, 0, None);
		System::assert_last_event(
			ProxyEvent::PureCreated {
				pure: anon,
				who: 1,
				proxy_type: ProxyType::Any,
				disambiguation_index: 0,
			}
			.into(),
		);

		// other calls to pure allowed as long as they're not exactly the same.
		assert_ok!(Proxy::create_pure(RuntimeOrigin::signed(1), ProxyType::JustTransfer, 0, 0));
		assert_ok!(Proxy::create_pure(RuntimeOrigin::signed(1), ProxyType::Any, 0, 1));
		let anon2 = Proxy::pure_account(&2, &ProxyType::Any, 0, None);
		assert_ok!(Proxy::create_pure(RuntimeOrigin::signed(2), ProxyType::Any, 0, 0));
		assert_noop!(
			Proxy::create_pure(RuntimeOrigin::signed(1), ProxyType::Any, 0, 0),
			Error::<Test>::Duplicate
		);
		System::set_extrinsic_index(1);
		assert_ok!(Proxy::create_pure(RuntimeOrigin::signed(1), ProxyType::Any, 0, 0));
		System::set_extrinsic_index(0);
		System::set_block_number(2);
		assert_ok!(Proxy::create_pure(RuntimeOrigin::signed(1), ProxyType::Any, 0, 0));

		let call = Box::new(call_transfer(6, 1));
		assert_ok!(Balances::transfer_allow_death(RuntimeOrigin::signed(3), anon, 5));
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(1), anon, None, call));
		System::assert_last_event(ProxyEvent::ProxyExecuted { result: Ok(()) }.into());
		assert_eq!(Balances::free_balance(6), 1);

		let call = Box::new(RuntimeCall::Proxy(ProxyCall::new_call_variant_kill_pure(
			1,
			ProxyType::Any,
			0,
			1,
			0,
		)));
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(2), anon2, None, call.clone()));
		let de = DispatchError::from(Error::<Test>::NoPermission).stripped();
		System::assert_last_event(ProxyEvent::ProxyExecuted { result: Err(de) }.into());
		assert_noop!(
			Proxy::kill_pure(RuntimeOrigin::signed(1), 1, ProxyType::Any, 0, 1, 0),
			Error::<Test>::NoPermission
		);
		assert_eq!(Balances::free_balance(1), 1);
		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(1), anon, None, call.clone()));
		assert_eq!(Balances::free_balance(1), 3);
		assert_noop!(
			Proxy::proxy(RuntimeOrigin::signed(1), anon, None, call.clone()),
			Error::<Test>::NotProxy
		);
	});
}
