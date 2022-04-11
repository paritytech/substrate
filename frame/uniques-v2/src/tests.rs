// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use crate::{mock::*, *};
use enumflags2::BitFlags;

use frame_support::{assert_noop, assert_ok};

fn get_id_from_event() -> Result<<Test as Config>::CollectionId, &'static str> {
	let last_event = System::events().pop();
	if let Some(e) = last_event.clone() {
		match e.event {
			mock::Event::Uniques(inner_event) => match inner_event {
				Event::CollectionCreated {
					id,
					max_supply: _,
					creator: _,
					owner: _,
				} => {
					return Ok(id)
				},
				_ => {},
			},
			_ => {},
		}
	}

	Err("bad event")
}

fn events() -> Vec<Event<Test>> {
	let result = System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let mock::Event::Uniques(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>();

	System::reset_events();

	result
}

fn collections() -> Vec<(u64, u32)> {
	let mut r: Vec<_> = CollectionOwner::<Test>::iter().map(|x| (x.0, x.1)).collect();
	r.sort();
	let mut s: Vec<_> = Collections::<Test>::iter().map(|x| (x.1.owner, x.0)).collect();
	s.sort();
	assert_eq!(r, s);
	r
}

pub const DEFAULT_SYSTEM_FEATURES: SystemFeatures = SystemFeatures::NoDeposit;
pub const DEFAULT_USER_FEATURES: UserFeatures = UserFeatures::Administration;


#[test]
fn minting_should_work() {
	new_test_ext().execute_with(|| {
		let owner = 1;
		let creator = 1;
		assert_ok!(
			Uniques::create(
				Origin::signed(creator),
				owner,
				DEFAULT_USER_FEATURES,
				None,
				None,
			)
		);

		let id = get_id_from_event().unwrap();
		let collection_config = CollectionConfigs::<Test>::get(id);

		let expected_config = CollectionConfig {
			system_features: DEFAULT_SYSTEM_FEATURES,
			user_features: DEFAULT_USER_FEATURES,
		};
		assert_eq!(Some(expected_config), collection_config);

		assert_eq!(events(), [
			Event::<Test>::CollectionCreated {
				id,
				max_supply: None,
				owner,
				creator,
			}
		]);
		assert_eq!(CountForCollections::<Test>::get(), 1);
		assert!(CollectionCreator::<Test>::contains_key(creator, id));
		assert_eq!(collections(), vec![(owner, id)]);
	});
}

#[test]
fn collection_locking_should_work() {
	new_test_ext().execute_with(|| {
		let user_id = 1;

		assert_ok!(
			Uniques::create(
				Origin::signed(user_id),
				user_id,
				DEFAULT_USER_FEATURES,
				None,
				None,
			)
		);

		let id = get_id_from_event().unwrap();
		let new_config = UserFeatures::IsLocked;

		assert_ok!(Uniques::change_collection_config(Origin::signed(user_id), id, new_config));

		let collection_config = CollectionConfigs::<Test>::get(id);

		let expected_config = CollectionConfig {
			system_features: DEFAULT_SYSTEM_FEATURES,
			user_features: new_config,
		};

		assert_eq!(Some(expected_config), collection_config);
	});
}

#[test]
fn collection_locking_should_fail() {
	new_test_ext().execute_with(|| {
		let user_id = 1;
		let user_features = UserFeatures::IsLocked;

		assert_ok!(Uniques::create(Origin::signed(user_id), user_id, user_features, None, None));

		let id = get_id_from_event().unwrap();
		let new_config = UserFeatures::Administration;

		assert!(events().contains(&Event::<Test>::CollectionLocked { id }));

		assert_noop!(
			Uniques::change_collection_config(Origin::signed(user_id), id, new_config),
			Error::<Test>::CollectionIsLocked,
		);
	});
}

#[test]
fn update_max_supply_should_work() {
	new_test_ext().execute_with(|| {
		let id = 0;
		let user_id = 1;
		let max_supply = Some(10);

		assert_ok!(
			Uniques::create(
				Origin::signed(user_id),
				user_id,
				DEFAULT_USER_FEATURES,
				max_supply,
				None,
			)
		);

		let collection = Collections::<Test>::get(id).unwrap();
		assert_eq!(collection.max_supply, max_supply);

		let new_max_supply = Some(10);
		assert_ok!(Uniques::update_max_supply(Origin::signed(user_id), id, new_max_supply));

		let collection = Collections::<Test>::get(id).unwrap();
		assert_eq!(collection.max_supply, new_max_supply);

		assert!(events().contains(
			&Event::<Test>::CollectionMaxSupplyChanged { id, max_supply: new_max_supply }
		));
	});
}

#[test]
fn different_user_flags() {
	new_test_ext().execute_with(|| {
		// TODO: try to pass an empty value
		// TODO: try to pass combined flags

		// TODO: uncomment
		// let user_features = UserFeatures::Administration | UserFeatures::IsLocked;
		// assert_ok!(Uniques::create(Origin::signed(1), 1, BitFlags::EMPTY, None, None));

		let user_features = UserFeatures::IsLocked;
		assert_ok!(Uniques::create(Origin::signed(1), 1, user_features, None, None));
	});
}

