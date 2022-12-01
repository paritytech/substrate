// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Tests for the module.

use super::*;
use frame_support::{assert_noop, assert_ok};
use mock::{
	new_test_ext, Call, Event as TestEvent, Logger, LoggerCall, Origin, Sudo, SudoCall, System,
	Test,
};

#[test]
fn test_setup_works() {
	// Environment setup, logger storage, and sudo `key` retrieval should work as expected.
	new_test_ext(1).execute_with(|| {
		assert_eq!(Sudo::key(), 1u64);
		assert!(Logger::i32_log().is_empty());
		assert!(Logger::account_log().is_empty());
	});
}

#[test]
fn sudo_basics() {
	// Configure a default test environment and set the root `key` to 1.
	new_test_ext(1).execute_with(|| {
		// A privileged function should work when `sudo` is passed the root `key` as `origin`.
		let call = Box::new(Call::Logger(LoggerCall::privileged_i32_log { i: 42, weight: 1_000 }));
		assert_ok!(Sudo::sudo(Origin::signed(1), call));
		assert_eq!(Logger::i32_log(), vec![42i32]);

		// A privileged function should not work when `sudo` is passed a non-root `key` as `origin`.
		let call = Box::new(Call::Logger(LoggerCall::privileged_i32_log { i: 42, weight: 1_000 }));
		assert_noop!(Sudo::sudo(Origin::signed(2), call), Error::<Test>::RequireSudo);
	});
}

#[test]
fn sudo_emits_events_correctly() {
	new_test_ext(1).execute_with(|| {
		// Set block number to 1 because events are not emitted on block 0.
		System::set_block_number(1);

		// Should emit event to indicate success when called with the root `key` and `call` is `Ok`.
		let call = Box::new(Call::Logger(LoggerCall::privileged_i32_log { i: 42, weight: 1 }));
		assert_ok!(Sudo::sudo(Origin::signed(1), call));
		System::assert_has_event(TestEvent::Sudo(Event::Sudid(Ok(()))));
	})
}

#[test]
fn sudo_unchecked_weight_basics() {
	new_test_ext(1).execute_with(|| {
		// A privileged function should work when `sudo` is passed the root `key` as origin.
		let call = Box::new(Call::Logger(LoggerCall::privileged_i32_log { i: 42, weight: 1_000 }));
		assert_ok!(Sudo::sudo_unchecked_weight(Origin::signed(1), call, 1_000));
		assert_eq!(Logger::i32_log(), vec![42i32]);

		// A privileged function should not work when called with a non-root `key`.
		let call = Box::new(Call::Logger(LoggerCall::privileged_i32_log { i: 42, weight: 1_000 }));
		assert_noop!(
			Sudo::sudo_unchecked_weight(Origin::signed(2), call, 1_000),
			Error::<Test>::RequireSudo,
		);
		// `I32Log` is unchanged after unsuccessful call.
		assert_eq!(Logger::i32_log(), vec![42i32]);

		// Controls the dispatched weight.
		let call = Box::new(Call::Logger(LoggerCall::privileged_i32_log { i: 42, weight: 1 }));
		let sudo_unchecked_weight_call = SudoCall::sudo_unchecked_weight { call, weight: 1_000 };
		let info = sudo_unchecked_weight_call.get_dispatch_info();
		assert_eq!(info.weight, 1_000);
	});
}

#[test]
fn sudo_unchecked_weight_emits_events_correctly() {
	new_test_ext(1).execute_with(|| {
		// Set block number to 1 because events are not emitted on block 0.
		System::set_block_number(1);

		// Should emit event to indicate success when called with the root `key` and `call` is `Ok`.
		let call = Box::new(Call::Logger(LoggerCall::privileged_i32_log { i: 42, weight: 1 }));
		assert_ok!(Sudo::sudo_unchecked_weight(Origin::signed(1), call, 1_000));
		System::assert_has_event(TestEvent::Sudo(Event::Sudid(Ok(()))));
	})
}

#[test]
fn set_key_basics() {
	new_test_ext(1).execute_with(|| {
		// A root `key` can change the root `key`
		assert_ok!(Sudo::set_key(Origin::signed(1), 2));
		assert_eq!(Sudo::key(), 2u64);
	});

	new_test_ext(1).execute_with(|| {
		// A non-root `key` will trigger a `RequireSudo` error and a non-root `key` cannot change
		// the root `key`.
		assert_noop!(Sudo::set_key(Origin::signed(2), 3), Error::<Test>::RequireSudo);
	});
}

#[test]
fn set_key_emits_events_correctly() {
	new_test_ext(1).execute_with(|| {
		// Set block number to 1 because events are not emitted on block 0.
		System::set_block_number(1);

		// A root `key` can change the root `key`.
		assert_ok!(Sudo::set_key(Origin::signed(1), 2));
		System::assert_has_event(TestEvent::Sudo(Event::KeyChanged(1)));
		// Double check.
		assert_ok!(Sudo::set_key(Origin::signed(2), 4));
		System::assert_has_event(TestEvent::Sudo(Event::KeyChanged(2)));
	});
}

#[test]
fn sudo_as_basics() {
	new_test_ext(1).execute_with(|| {
		// A privileged function will not work when passed to `sudo_as`.
		let call = Box::new(Call::Logger(LoggerCall::privileged_i32_log { i: 42, weight: 1_000 }));
		assert_ok!(Sudo::sudo_as(Origin::signed(1), 2, call));
		assert!(Logger::i32_log().is_empty());
		assert!(Logger::account_log().is_empty());

		// A non-privileged function should not work when called with a non-root `key`.
		let call = Box::new(Call::Logger(LoggerCall::non_privileged_log { i: 42, weight: 1 }));
		assert_noop!(Sudo::sudo_as(Origin::signed(3), 2, call), Error::<Test>::RequireSudo);

		// A non-privileged function will work when passed to `sudo_as` with the root `key`.
		let call = Box::new(Call::Logger(LoggerCall::non_privileged_log { i: 42, weight: 1 }));
		assert_ok!(Sudo::sudo_as(Origin::signed(1), 2, call));
		assert_eq!(Logger::i32_log(), vec![42i32]);
		// The correct user makes the call within `sudo_as`.
		assert_eq!(Logger::account_log(), vec![2]);
	});
}

#[test]
fn sudo_as_emits_events_correctly() {
	new_test_ext(1).execute_with(|| {
		// Set block number to 1 because events are not emitted on block 0.
		System::set_block_number(1);

		// A non-privileged function will work when passed to `sudo_as` with the root `key`.
		let call = Box::new(Call::Logger(LoggerCall::non_privileged_log { i: 42, weight: 1 }));
		assert_ok!(Sudo::sudo_as(Origin::signed(1), 2, call));
		System::assert_has_event(TestEvent::Sudo(Event::SudoAsDone(Ok(()))));
	});
}
