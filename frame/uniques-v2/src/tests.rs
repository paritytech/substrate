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

use frame_support::assert_ok;

fn get_id_from_event() -> Result<<Test as Config>::CollectionId, &'static str> {
	let last_event = System::events().pop();
	if let Some(e) = last_event.clone() {
		match e.event {
			mock::Event::Uniques(inner_event) => match inner_event {
				Event::CollectionCreated { id, max_supply: _ } => {
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

#[test]
fn sanity_test() {
	new_test_ext().execute_with(|| {
		let user_features = UserFeatures::Administration;
		assert_ok!(Uniques::create(Origin::signed(1), user_features, None, None));

		let id = get_id_from_event().unwrap();
		let collection_config = CollectionConfigs::<Test>::get(id);

		let expected_config =
			CollectionConfig { system_features: SystemFeatures::NoDeposit, user_features };
		assert_eq!(Some(expected_config), collection_config)
	});
}

#[test]
fn basic_minting_should_work() {
	new_test_ext().execute_with(|| {
		let user_features = UserFeatures::Administration | UserFeatures::IsLocked;
		// TODO: try to pass an empty value
		// TODO: try to pass combined flags
		assert_ok!(Uniques::create(Origin::signed(1), BitFlags::EMPTY, None, None));
		assert!(events().contains(&Event::<Test>::CollectionLocked { id: 0 }));
	});
}

