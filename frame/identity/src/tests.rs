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

// Tests for Identity Pallet

use super::*;
use crate as pallet_identity;

use sp_runtime::traits::BadOrigin;
use frame_support::{assert_ok, assert_noop, parameter_types, ord_parameter_types};
use sp_core::H256;
use frame_system::{EnsureSignedBy, EnsureOneOf, EnsureRoot};
use sp_runtime::{
	testing::Header, traits::{BlakeTwo256, IdentityLookup},
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Identity: pallet_identity::{Pallet, Call, Storage, Event<T>},
	}
);

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1024);
}
impl frame_system::Config for Test {
	type BaseCallFilter = ();
	type BlockWeights = ();
	type BlockLength = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Call = Call;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
}
parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}
impl pallet_balances::Config for Test {
	type Balance = u64;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type MaxLocks = ();
	type WeightInfo = ();
}
parameter_types! {
	pub const BasicDeposit: u64 = 10;
	pub const FieldDeposit: u64 = 10;
	pub const SubAccountDeposit: u64 = 10;
	pub const MaxSubAccounts: u32 = 2;
	pub const MaxAdditionalFields: u32 = 2;
	pub const MaxRegistrars: u32 = 20;
}
ord_parameter_types! {
	pub const One: u64 = 1;
	pub const Two: u64 = 2;
}
type EnsureOneOrRoot = EnsureOneOf<
	u64,
	EnsureRoot<u64>,
	EnsureSignedBy<One, u64>
>;
type EnsureTwoOrRoot = EnsureOneOf<
	u64,
	EnsureRoot<u64>,
	EnsureSignedBy<Two, u64>
>;
impl Config for Test {
	type Event = Event;
	type Currency = Balances;
	type Slashed = ();
	type BasicDeposit = BasicDeposit;
	type FieldDeposit = FieldDeposit;
	type SubAccountDeposit = SubAccountDeposit;
	type MaxSubAccounts = MaxSubAccounts;
	type MaxAdditionalFields = MaxAdditionalFields;
	type MaxRegistrars = MaxRegistrars;
	type RegistrarOrigin = EnsureOneOrRoot;
	type ForceOrigin = EnsureTwoOrRoot;
	type WeightInfo = ();
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test> {
		balances: vec![
			(1, 10),
			(2, 10),
			(3, 10),
			(10, 100),
			(20, 100),
			(30, 100),
		],
	}.assimilate_storage(&mut t).unwrap();
	t.into()
}

fn ten() -> IdentityInfo {
	IdentityInfo {
		display: Data::Raw(b"ten".to_vec()),
		legal: Data::Raw(b"The Right Ordinal Ten, Esq.".to_vec()),
		.. Default::default()
	}
}

fn twenty() -> IdentityInfo {
	IdentityInfo {
		display: Data::Raw(b"twenty".to_vec()),
		legal: Data::Raw(b"The Right Ordinal Twenty, Esq.".to_vec()),
		.. Default::default()
	}
}

#[test]
fn editing_subaccounts_should_work() {
	new_test_ext().execute_with(|| {
		let data = |x| Data::Raw(vec![x; 1]);

		assert_noop!(Identity::add_sub(Origin::signed(10), 20, data(1)), Error::<Test>::NoIdentity);

		assert_ok!(Identity::set_identity(Origin::signed(10), ten()));

		// first sub account
		assert_ok!(Identity::add_sub(Origin::signed(10), 1, data(1)));
		assert_eq!(SuperOf::<Test>::get(1), Some((10, data(1))));
		assert_eq!(Balances::free_balance(10), 80);

		// second sub account
		assert_ok!(Identity::add_sub(Origin::signed(10), 2, data(2)));
		assert_eq!(SuperOf::<Test>::get(1), Some((10, data(1))));
		assert_eq!(SuperOf::<Test>::get(2), Some((10, data(2))));
		assert_eq!(Balances::free_balance(10), 70);

		// third sub account is too many
		assert_noop!(Identity::add_sub(Origin::signed(10), 3, data(3)), Error::<Test>::TooManySubAccounts);

		// rename first sub account
		assert_ok!(Identity::rename_sub(Origin::signed(10), 1, data(11)));
		assert_eq!(SuperOf::<Test>::get(1), Some((10, data(11))));
		assert_eq!(SuperOf::<Test>::get(2), Some((10, data(2))));
		assert_eq!(Balances::free_balance(10), 70);

		// remove first sub account
		assert_ok!(Identity::remove_sub(Origin::signed(10), 1));
		assert_eq!(SuperOf::<Test>::get(1), None);
		assert_eq!(SuperOf::<Test>::get(2), Some((10, data(2))));
		assert_eq!(Balances::free_balance(10), 80);

		// add third sub account
		assert_ok!(Identity::add_sub(Origin::signed(10), 3, data(3)));
		assert_eq!(SuperOf::<Test>::get(1), None);
		assert_eq!(SuperOf::<Test>::get(2), Some((10, data(2))));
		assert_eq!(SuperOf::<Test>::get(3), Some((10, data(3))));
		assert_eq!(Balances::free_balance(10), 70);
	});
}

#[test]
fn resolving_subaccount_ownership_works() {
	new_test_ext().execute_with(|| {
		let data = |x| Data::Raw(vec![x; 1]);

		assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
		assert_ok!(Identity::set_identity(Origin::signed(20), twenty()));

		// 10 claims 1 as a subaccount
		assert_ok!(Identity::add_sub(Origin::signed(10), 1, data(1)));
		assert_eq!(Balances::free_balance(1), 10);
		assert_eq!(Balances::free_balance(10), 80);
		assert_eq!(Balances::reserved_balance(10), 20);
		// 20 cannot claim 1 now
		assert_noop!(Identity::add_sub(Origin::signed(20), 1, data(1)), Error::<Test>::AlreadyClaimed);
		// 1 wants to be with 20 so it quits from 10
		assert_ok!(Identity::quit_sub(Origin::signed(1)));
		// 1 gets the 10 that 10 paid.
		assert_eq!(Balances::free_balance(1), 20);
		assert_eq!(Balances::free_balance(10), 80);
		assert_eq!(Balances::reserved_balance(10), 10);
		// 20 can claim 1 now
		assert_ok!(Identity::add_sub(Origin::signed(20), 1, data(1)));
	});
}

#[test]
fn trailing_zeros_decodes_into_default_data() {
	let encoded = Data::Raw(b"Hello".to_vec()).encode();
	assert!(<(Data, Data)>::decode(&mut &encoded[..]).is_err());
	let input = &mut &encoded[..];
	let (a, b) = <(Data, Data)>::decode(&mut AppendZerosInput::new(input)).unwrap();
	assert_eq!(a, Data::Raw(b"Hello".to_vec()));
	assert_eq!(b, Data::None);
}

#[test]
fn adding_registrar_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
		assert_ok!(Identity::set_fee(Origin::signed(3), 0, 10));
		let fields = IdentityFields(IdentityField::Display | IdentityField::Legal);
		assert_ok!(Identity::set_fields(Origin::signed(3), 0, fields));
		assert_eq!(Identity::registrars(), vec![
			Some(RegistrarInfo { account: 3, fee: 10, fields })
		]);
	});
}

#[test]
fn amount_of_registrars_is_limited() {
	new_test_ext().execute_with(|| {
		for i in 1..MaxRegistrars::get() + 1 {
			assert_ok!(Identity::add_registrar(Origin::signed(1), i as u64));
		}
		let last_registrar = MaxRegistrars::get() as u64 + 1;
		assert_noop!(
			Identity::add_registrar(Origin::signed(1), last_registrar),
			Error::<Test>::TooManyRegistrars
		);
	});
}

#[test]
fn registration_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
		assert_ok!(Identity::set_fee(Origin::signed(3), 0, 10));
		let mut three_fields = ten();
		three_fields.additional.push(Default::default());
		three_fields.additional.push(Default::default());
		three_fields.additional.push(Default::default());
		assert_noop!(
			Identity::set_identity(Origin::signed(10), three_fields),
			Error::<Test>::TooManyFields
		);
		assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
		assert_eq!(Identity::identity(10).unwrap().info, ten());
		assert_eq!(Balances::free_balance(10), 90);
		assert_ok!(Identity::clear_identity(Origin::signed(10)));
		assert_eq!(Balances::free_balance(10), 100);
		assert_noop!(Identity::clear_identity(Origin::signed(10)), Error::<Test>::NotNamed);
	});
}

#[test]
fn uninvited_judgement_should_work() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::Reasonable),
			Error::<Test>::InvalidIndex
		);

		assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
		assert_noop!(
			Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::Reasonable),
			Error::<Test>::InvalidTarget
		);

		assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
		assert_noop!(
			Identity::provide_judgement(Origin::signed(10), 0, 10, Judgement::Reasonable),
			Error::<Test>::InvalidIndex
		);
		assert_noop!(
			Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::FeePaid(1)),
			Error::<Test>::InvalidJudgement
		);

		assert_ok!(Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::Reasonable));
		assert_eq!(Identity::identity(10).unwrap().judgements, vec![(0, Judgement::Reasonable)]);
	});
}

#[test]
fn clearing_judgement_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
		assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
		assert_ok!(Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::Reasonable));
		assert_ok!(Identity::clear_identity(Origin::signed(10)));
		assert_eq!(Identity::identity(10), None);
	});
}

#[test]
fn killing_slashing_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
		assert_noop!(Identity::kill_identity(Origin::signed(1), 10), BadOrigin);
		assert_ok!(Identity::kill_identity(Origin::signed(2), 10));
		assert_eq!(Identity::identity(10), None);
		assert_eq!(Balances::free_balance(10), 90);
		assert_noop!(Identity::kill_identity(Origin::signed(2), 10), Error::<Test>::NotNamed);
	});
}

#[test]
fn setting_subaccounts_should_work() {
	new_test_ext().execute_with(|| {
		let mut subs = vec![(20, Data::Raw(vec![40; 1]))];
		assert_noop!(Identity::set_subs(Origin::signed(10), subs.clone()), Error::<Test>::NotFound);

		assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
		assert_ok!(Identity::set_subs(Origin::signed(10), subs.clone()));
		assert_eq!(Balances::free_balance(10), 80);
		assert_eq!(Identity::subs_of(10), (10, vec![20]));
		assert_eq!(Identity::super_of(20), Some((10, Data::Raw(vec![40; 1]))));

		// push another item and re-set it.
		subs.push((30, Data::Raw(vec![50; 1])));
		assert_ok!(Identity::set_subs(Origin::signed(10), subs.clone()));
		assert_eq!(Balances::free_balance(10), 70);
		assert_eq!(Identity::subs_of(10), (20, vec![20, 30]));
		assert_eq!(Identity::super_of(20), Some((10, Data::Raw(vec![40; 1]))));
		assert_eq!(Identity::super_of(30), Some((10, Data::Raw(vec![50; 1]))));

		// switch out one of the items and re-set.
		subs[0] = (40, Data::Raw(vec![60; 1]));
		assert_ok!(Identity::set_subs(Origin::signed(10), subs.clone()));
		assert_eq!(Balances::free_balance(10), 70); // no change in the balance
		assert_eq!(Identity::subs_of(10), (20, vec![40, 30]));
		assert_eq!(Identity::super_of(20), None);
		assert_eq!(Identity::super_of(30), Some((10, Data::Raw(vec![50; 1]))));
		assert_eq!(Identity::super_of(40), Some((10, Data::Raw(vec![60; 1]))));

		// clear
		assert_ok!(Identity::set_subs(Origin::signed(10), vec![]));
		assert_eq!(Balances::free_balance(10), 90);
		assert_eq!(Identity::subs_of(10), (0, vec![]));
		assert_eq!(Identity::super_of(30), None);
		assert_eq!(Identity::super_of(40), None);

		subs.push((20, Data::Raw(vec![40; 1])));
		assert_noop!(Identity::set_subs(Origin::signed(10), subs.clone()), Error::<Test>::TooManySubAccounts);
	});
}

#[test]
fn clearing_account_should_remove_subaccounts_and_refund() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
		assert_ok!(Identity::set_subs(Origin::signed(10), vec![(20, Data::Raw(vec![40; 1]))]));
		assert_ok!(Identity::clear_identity(Origin::signed(10)));
		assert_eq!(Balances::free_balance(10), 100);
		assert!(Identity::super_of(20).is_none());
	});
}

#[test]
fn killing_account_should_remove_subaccounts_and_not_refund() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
		assert_ok!(Identity::set_subs(Origin::signed(10), vec![(20, Data::Raw(vec![40; 1]))]));
		assert_ok!(Identity::kill_identity(Origin::signed(2), 10));
		assert_eq!(Balances::free_balance(10), 80);
		assert!(Identity::super_of(20).is_none());
	});
}

#[test]
fn cancelling_requested_judgement_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
		assert_ok!(Identity::set_fee(Origin::signed(3), 0, 10));
		assert_noop!(Identity::cancel_request(Origin::signed(10), 0), Error::<Test>::NoIdentity);
		assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
		assert_ok!(Identity::request_judgement(Origin::signed(10), 0, 10));
		assert_ok!(Identity::cancel_request(Origin::signed(10), 0));
		assert_eq!(Balances::free_balance(10), 90);
		assert_noop!(Identity::cancel_request(Origin::signed(10), 0), Error::<Test>::NotFound);

		assert_ok!(Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::Reasonable));
		assert_noop!(Identity::cancel_request(Origin::signed(10), 0), Error::<Test>::JudgementGiven);
	});
}

#[test]
fn requesting_judgement_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
		assert_ok!(Identity::set_fee(Origin::signed(3), 0, 10));
		assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
		assert_noop!(Identity::request_judgement(Origin::signed(10), 0, 9), Error::<Test>::FeeChanged);
		assert_ok!(Identity::request_judgement(Origin::signed(10), 0, 10));
		// 10 for the judgement request, 10 for the identity.
		assert_eq!(Balances::free_balance(10), 80);

		// Re-requesting won't work as we already paid.
		assert_noop!(Identity::request_judgement(Origin::signed(10), 0, 10), Error::<Test>::StickyJudgement);
		assert_ok!(Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::Erroneous));
		// Registrar got their payment now.
		assert_eq!(Balances::free_balance(3), 20);

		// Re-requesting still won't work as it's erroneous.
		assert_noop!(Identity::request_judgement(Origin::signed(10), 0, 10), Error::<Test>::StickyJudgement);

		// Requesting from a second registrar still works.
		assert_ok!(Identity::add_registrar(Origin::signed(1), 4));
		assert_ok!(Identity::request_judgement(Origin::signed(10), 1, 10));

		// Re-requesting after the judgement has been reduced works.
		assert_ok!(Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::OutOfDate));
		assert_ok!(Identity::request_judgement(Origin::signed(10), 0, 10));
	});
}

#[test]
fn field_deposit_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
		assert_ok!(Identity::set_fee(Origin::signed(3), 0, 10));
		assert_ok!(Identity::set_identity(Origin::signed(10), IdentityInfo {
			additional: vec![
				(Data::Raw(b"number".to_vec()), Data::Raw(10u32.encode())),
				(Data::Raw(b"text".to_vec()), Data::Raw(b"10".to_vec())),
			], .. Default::default()
		}));
		assert_eq!(Balances::free_balance(10), 70);
	});
}

#[test]
fn setting_account_id_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
		// account 4 cannot change the first registrar's identity since it's owned by 3.
		assert_noop!(Identity::set_account_id(Origin::signed(4), 0, 3), Error::<Test>::InvalidIndex);
		// account 3 can, because that's the registrar's current account.
		assert_ok!(Identity::set_account_id(Origin::signed(3), 0, 4));
		// account 4 can now, because that's their new ID.
		assert_ok!(Identity::set_account_id(Origin::signed(4), 0, 3));
	});
}
