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

//! Tests for remarks pallet.

use super::{Error, Event, Pallet as Remark};
use crate::mock::*;
use frame_support::{assert_noop, assert_ok};
use frame_system::RawOrigin;

#[test]
fn generates_event() {
	new_test_ext().execute_with(|| {
		let caller = 1;
		let data = vec![0u8; 100];
		System::set_block_number(System::block_number() + 1); //otherwise event won't be registered.
		assert_ok!(Remark::<Test>::store(RawOrigin::Signed(caller).into(), data.clone(),));
		let events = System::events();
		// this one we create as we expect it
		let system_event: <Test as frame_system::Config>::RuntimeEvent = Event::Stored {
			content_hash: sp_io::hashing::blake2_256(&data).into(),
			sender: caller,
		}
		.into();
		// this one we actually go into the system pallet and get the last event
		// because we know its there from block +1
		let frame_system::EventRecord { event, .. } = &events[events.len() - 1];
		assert_eq!(event, &system_event);
	});
}

#[test]
fn does_not_store_empty() {
	new_test_ext().execute_with(|| {
		let caller = 1;
		let data = vec![];
		System::set_block_number(System::block_number() + 1); //otherwise event won't be registered.
		assert_noop!(
			Remark::<Test>::store(RawOrigin::Signed(caller).into(), data.clone(),),
			Error::<Test>::Empty
		);
		assert!(System::events().is_empty());
	});
}
