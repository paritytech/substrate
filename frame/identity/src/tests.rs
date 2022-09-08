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

// Tests for Identity Pallet

use super::*;
use crate as pallet_identity;

use codec::{Decode, Encode};
use frame_support::{
	assert_noop, assert_ok, ord_parameter_types, parameter_types,
	traits::{ConstU32, ConstU64, EitherOfDiverse},
	BoundedVec,
};
use frame_system::{EnsureRoot, EnsureSignedBy};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BadOrigin, BlakeTwo256, IdentityLookup},
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
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(frame_support::weights::Weight::from_ref_time(1024));
}
impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
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
	type BlockHashCount = ConstU64<250>;
	type DbWeight = ();
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
	type Balance = u64;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type WeightInfo = ();
}

parameter_types! {
	pub const MaxAdditionalFields: u32 = 2;
	pub const MaxRegistrars: u32 = 20;
}

ord_parameter_types! {
	pub const One: u64 = 1;
	pub const Two: u64 = 2;
}
type EnsureOneOrRoot = EitherOfDiverse<EnsureRoot<u64>, EnsureSignedBy<One, u64>>;
type EnsureTwoOrRoot = EitherOfDiverse<EnsureRoot<u64>, EnsureSignedBy<Two, u64>>;
impl pallet_identity::Config for Test {
	type Event = Event;
	type Currency = Balances;
	type Slashed = ();
	type BasicDeposit = ConstU64<10>;
	type FieldDeposit = ConstU64<10>;
	type SubAccountDeposit = ConstU64<10>;
	type MaxSubAccounts = ConstU32<2>;
	type MaxAdditionalFields = MaxAdditionalFields;
	type MaxRegistrars = MaxRegistrars;
	type RegistrarOrigin = EnsureOneOrRoot;
	type ForceOrigin = EnsureTwoOrRoot;
	type WeightInfo = ();
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test> {
		balances: vec![(1, 10), (2, 10), (3, 10), (10, 100), (20, 100), (30, 100)],
	}
	.assimilate_storage(&mut t)
	.unwrap();
	t.into()
}

fn ten() -> IdentityInfo<MaxAdditionalFields> {
	IdentityInfo {
		display: Data::Raw(b"ten".to_vec().try_into().unwrap()),
		legal: Data::Raw(b"The Right Ordinal Ten, Esq.".to_vec().try_into().unwrap()),
		..Default::default()
	}
}

fn twenty() -> IdentityInfo<MaxAdditionalFields> {
	IdentityInfo {
		display: Data::Raw(b"twenty".to_vec().try_into().unwrap()),
		legal: Data::Raw(b"The Right Ordinal Twenty, Esq.".to_vec().try_into().unwrap()),
		..Default::default()
	}
}

#[test]
fn editing_subaccounts_should_work() {
	new_test_ext().execute_with(|| {
		let data = |x| Data::Raw(vec![x; 1].try_into().unwrap());

		assert_noop!(Identity::add_sub(Origin::signed(10), 20, data(1)), Error::<Test>::NoIdentity);

		assert_ok!(Identity::set_identity(Origin::signed(10), Box::new(ten())));

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
		assert_noop!(
			Identity::add_sub(Origin::signed(10), 3, data(3)),
			Error::<Test>::TooManySubAccounts
		);

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
		let data = |x| Data::Raw(vec![x; 1].try_into().unwrap());

		assert_ok!(Identity::set_identity(Origin::signed(10), Box::new(ten())));
		assert_ok!(Identity::set_identity(Origin::signed(20), Box::new(twenty())));

		// 10 claims 1 as a subaccount
		assert_ok!(Identity::add_sub(Origin::signed(10), 1, data(1)));
		assert_eq!(Balances::free_balance(1), 10);
		assert_eq!(Balances::free_balance(10), 80);
		assert_eq!(Balances::reserved_balance(10), 20);
		// 20 cannot claim 1 now
		assert_noop!(
			Identity::add_sub(Origin::signed(20), 1, data(1)),
			Error::<Test>::AlreadyClaimed
		);
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
	let encoded = Data::Raw(b"Hello".to_vec().try_into().unwrap()).encode();
	assert!(<(Data, Data)>::decode(&mut &encoded[..]).is_err());
	let input = &mut &encoded[..];
	let (a, b) = <(Data, Data)>::decode(&mut AppendZerosInput::new(input)).unwrap();
	assert_eq!(a, Data::Raw(b"Hello".to_vec().try_into().unwrap()));
	assert_eq!(b, Data::None);
}

#[test]
fn adding_registrar_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
		assert_ok!(Identity::set_fee(Origin::signed(3), 0, 10));
		let fields = IdentityFields(IdentityField::Display | IdentityField::Legal);
		assert_ok!(Identity::set_fields(Origin::signed(3), 0, fields));
		assert_eq!(
			Identity::registrars(),
			vec![Some(RegistrarInfo { account: 3, fee: 10, fields })]
		);
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
		three_fields.additional.try_push(Default::default()).unwrap();
		three_fields.additional.try_push(Default::default()).unwrap();
		assert_eq!(three_fields.additional.try_push(Default::default()), Err(()));
		assert_ok!(Identity::set_identity(Origin::signed(10), Box::new(ten())));
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
			Identity::provide_judgement(
				Origin::signed(3),
				0,
				10,
				Judgement::Reasonable,
				H256::random()
			),
			Error::<Test>::InvalidIndex
		);

		assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
		assert_noop!(
			Identity::provide_judgement(
				Origin::signed(3),
				0,
				10,
				Judgement::Reasonable,
				H256::random()
			),
			Error::<Test>::InvalidTarget
		);

		assert_ok!(Identity::set_identity(Origin::signed(10), Box::new(ten())));
		assert_noop!(
			Identity::provide_judgement(
				Origin::signed(3),
				0,
				10,
				Judgement::Reasonable,
				H256::random()
			),
			Error::<Test>::JudgementForDifferentIdentity
		);

		let identity_hash = BlakeTwo256::hash_of(&ten());

		assert_noop!(
			Identity::provide_judgement(
				Origin::signed(10),
				0,
				10,
				Judgement::Reasonable,
				identity_hash
			),
			Error::<Test>::InvalidIndex
		);
		assert_noop!(
			Identity::provide_judgement(
				Origin::signed(3),
				0,
				10,
				Judgement::FeePaid(1),
				identity_hash
			),
			Error::<Test>::InvalidJudgement
		);

		assert_ok!(Identity::provide_judgement(
			Origin::signed(3),
			0,
			10,
			Judgement::Reasonable,
			identity_hash
		));
		assert_eq!(Identity::identity(10).unwrap().judgements, vec![(0, Judgement::Reasonable)]);
	});
}

#[test]
fn clearing_judgement_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
		assert_ok!(Identity::set_identity(Origin::signed(10), Box::new(ten())));
		assert_ok!(Identity::provide_judgement(
			Origin::signed(3),
			0,
			10,
			Judgement::Reasonable,
			BlakeTwo256::hash_of(&ten())
		));
		assert_ok!(Identity::clear_identity(Origin::signed(10)));
		assert_eq!(Identity::identity(10), None);
	});
}

#[test]
fn killing_slashing_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::set_identity(Origin::signed(10), Box::new(ten())));
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
		let mut subs = vec![(20, Data::Raw(vec![40; 1].try_into().unwrap()))];
		assert_noop!(Identity::set_subs(Origin::signed(10), subs.clone()), Error::<Test>::NotFound);

		assert_ok!(Identity::set_identity(Origin::signed(10), Box::new(ten())));
		assert_ok!(Identity::set_subs(Origin::signed(10), subs.clone()));
		assert_eq!(Balances::free_balance(10), 80);
		assert_eq!(Identity::subs_of(10), (10, vec![20].try_into().unwrap()));
		assert_eq!(Identity::super_of(20), Some((10, Data::Raw(vec![40; 1].try_into().unwrap()))));

		// push another item and re-set it.
		subs.push((30, Data::Raw(vec![50; 1].try_into().unwrap())));
		assert_ok!(Identity::set_subs(Origin::signed(10), subs.clone()));
		assert_eq!(Balances::free_balance(10), 70);
		assert_eq!(Identity::subs_of(10), (20, vec![20, 30].try_into().unwrap()));
		assert_eq!(Identity::super_of(20), Some((10, Data::Raw(vec![40; 1].try_into().unwrap()))));
		assert_eq!(Identity::super_of(30), Some((10, Data::Raw(vec![50; 1].try_into().unwrap()))));

		// switch out one of the items and re-set.
		subs[0] = (40, Data::Raw(vec![60; 1].try_into().unwrap()));
		assert_ok!(Identity::set_subs(Origin::signed(10), subs.clone()));
		assert_eq!(Balances::free_balance(10), 70); // no change in the balance
		assert_eq!(Identity::subs_of(10), (20, vec![40, 30].try_into().unwrap()));
		assert_eq!(Identity::super_of(20), None);
		assert_eq!(Identity::super_of(30), Some((10, Data::Raw(vec![50; 1].try_into().unwrap()))));
		assert_eq!(Identity::super_of(40), Some((10, Data::Raw(vec![60; 1].try_into().unwrap()))));

		// clear
		assert_ok!(Identity::set_subs(Origin::signed(10), vec![]));
		assert_eq!(Balances::free_balance(10), 90);
		assert_eq!(Identity::subs_of(10), (0, BoundedVec::default()));
		assert_eq!(Identity::super_of(30), None);
		assert_eq!(Identity::super_of(40), None);

		subs.push((20, Data::Raw(vec![40; 1].try_into().unwrap())));
		assert_noop!(
			Identity::set_subs(Origin::signed(10), subs.clone()),
			Error::<Test>::TooManySubAccounts
		);
	});
}

#[test]
fn clearing_account_should_remove_subaccounts_and_refund() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::set_identity(Origin::signed(10), Box::new(ten())));
		assert_ok!(Identity::set_subs(
			Origin::signed(10),
			vec![(20, Data::Raw(vec![40; 1].try_into().unwrap()))]
		));
		assert_ok!(Identity::clear_identity(Origin::signed(10)));
		assert_eq!(Balances::free_balance(10), 100);
		assert!(Identity::super_of(20).is_none());
	});
}

#[test]
fn killing_account_should_remove_subaccounts_and_not_refund() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::set_identity(Origin::signed(10), Box::new(ten())));
		assert_ok!(Identity::set_subs(
			Origin::signed(10),
			vec![(20, Data::Raw(vec![40; 1].try_into().unwrap()))]
		));
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
		assert_ok!(Identity::set_identity(Origin::signed(10), Box::new(ten())));
		assert_ok!(Identity::request_judgement(Origin::signed(10), 0, 10));
		assert_ok!(Identity::cancel_request(Origin::signed(10), 0));
		assert_eq!(Balances::free_balance(10), 90);
		assert_noop!(Identity::cancel_request(Origin::signed(10), 0), Error::<Test>::NotFound);

		assert_ok!(Identity::provide_judgement(
			Origin::signed(3),
			0,
			10,
			Judgement::Reasonable,
			BlakeTwo256::hash_of(&ten())
		));
		assert_noop!(
			Identity::cancel_request(Origin::signed(10), 0),
			Error::<Test>::JudgementGiven
		);
	});
}

#[test]
fn requesting_judgement_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
		assert_ok!(Identity::set_fee(Origin::signed(3), 0, 10));
		assert_ok!(Identity::set_identity(Origin::signed(10), Box::new(ten())));
		assert_noop!(
			Identity::request_judgement(Origin::signed(10), 0, 9),
			Error::<Test>::FeeChanged
		);
		assert_ok!(Identity::request_judgement(Origin::signed(10), 0, 10));
		// 10 for the judgement request, 10 for the identity.
		assert_eq!(Balances::free_balance(10), 80);

		// Re-requesting won't work as we already paid.
		assert_noop!(
			Identity::request_judgement(Origin::signed(10), 0, 10),
			Error::<Test>::StickyJudgement
		);
		assert_ok!(Identity::provide_judgement(
			Origin::signed(3),
			0,
			10,
			Judgement::Erroneous,
			BlakeTwo256::hash_of(&ten())
		));
		// Registrar got their payment now.
		assert_eq!(Balances::free_balance(3), 20);

		// Re-requesting still won't work as it's erroneous.
		assert_noop!(
			Identity::request_judgement(Origin::signed(10), 0, 10),
			Error::<Test>::StickyJudgement
		);

		// Requesting from a second registrar still works.
		assert_ok!(Identity::add_registrar(Origin::signed(1), 4));
		assert_ok!(Identity::request_judgement(Origin::signed(10), 1, 10));

		// Re-requesting after the judgement has been reduced works.
		assert_ok!(Identity::provide_judgement(
			Origin::signed(3),
			0,
			10,
			Judgement::OutOfDate,
			BlakeTwo256::hash_of(&ten())
		));
		assert_ok!(Identity::request_judgement(Origin::signed(10), 0, 10));
	});
}

#[test]
fn field_deposit_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
		assert_ok!(Identity::set_fee(Origin::signed(3), 0, 10));
		assert_ok!(Identity::set_identity(
			Origin::signed(10),
			Box::new(IdentityInfo {
				additional: vec![
					(
						Data::Raw(b"number".to_vec().try_into().unwrap()),
						Data::Raw(10u32.encode().try_into().unwrap())
					),
					(
						Data::Raw(b"text".to_vec().try_into().unwrap()),
						Data::Raw(b"10".to_vec().try_into().unwrap())
					),
				]
				.try_into()
				.unwrap(),
				..Default::default()
			})
		));
		assert_eq!(Balances::free_balance(10), 70);
	});
}

#[test]
fn setting_account_id_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
		// account 4 cannot change the first registrar's identity since it's owned by 3.
		assert_noop!(
			Identity::set_account_id(Origin::signed(4), 0, 3),
			Error::<Test>::InvalidIndex
		);
		// account 3 can, because that's the registrar's current account.
		assert_ok!(Identity::set_account_id(Origin::signed(3), 0, 4));
		// account 4 can now, because that's their new ID.
		assert_ok!(Identity::set_account_id(Origin::signed(4), 0, 3));
	});
}

#[test]
fn test_has_identity() {
	new_test_ext().execute_with(|| {
		assert_ok!(Identity::set_identity(Origin::signed(10), Box::new(ten())));
		assert!(Identity::has_identity(&10, IdentityField::Display as u64));
		assert!(Identity::has_identity(&10, IdentityField::Legal as u64));
		assert!(Identity::has_identity(
			&10,
			IdentityField::Display as u64 | IdentityField::Legal as u64
		));
		assert!(!Identity::has_identity(
			&10,
			IdentityField::Display as u64 | IdentityField::Legal as u64 | IdentityField::Web as u64
		));
	});
}
