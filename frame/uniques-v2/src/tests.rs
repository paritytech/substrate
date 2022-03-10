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

use frame_support::assert_ok;

fn get_id_from_event() -> Result<CollectionIdOf<Test>, &'static str> {
	let last_event = System::events().pop();
	if let Some(e) = last_event.clone() {
		match e.event {
			mock::Event::Uniques(inner_event) => match inner_event {
				Event::CollectionCreated { id } => {
					return Ok(id)
				},
				_ => {},
			},
			_ => {},
		}
	}

	Err("bad event")
}

#[test]
fn sanity_test() {
	new_test_ext().execute_with(|| {
		let user_features = UserFeatures::Administration;
		assert_ok!(Uniques::create(Origin::signed(1), None, user_features));

		let id = get_id_from_event().unwrap();
		let token_config = TokenConfigs::<Test>::get(id);

		let expected_config =
			TokenConfig { system_features: SystemFeatures::NoDeposit, user_features };
		assert_eq!(Some(expected_config), token_config)
	});
}
