// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Tests for the module.

use super::*;
use mock::{ Sudo, SudoCall, Origin, Call, Test, new_test_ext, logger, LoggerCall,
	Logger, TestEvent, System }; 
use frame_support::{assert_ok, assert_noop};

// #[test]
// fn new_test_ext_and_sudo_get_key_works() {
// 	// Test that the environment setup and pallets `key` retrieval works as expected.
// 	new_test_ext(1).execute_with(|| {
// 		assert_eq!(Sudo::key(),  1u64);
// 	});
// }

// #[test]
// fn sudo_basics() {
// 	// Configure a default test environment and set the root `key` to 1.
// 	new_test_ext(1).execute_with(|| {
// 		// A privileged function should work when `sudo` is passed the root `key` as `origin`.
// 		let call = Box::new(Call::Logger(LoggerCall::log(42, 1)));
// 		assert_ok!(Sudo::sudo(Origin::signed(1), call));
// 		assert_eq!(logger::log(), vec![42i32]); 
		
// 		// A privileged function should not work when `sudo` is passed a non-root `key` as `origin`.
// 		let call = Box::new(Call::Logger(LoggerCall::log(42, 1)));
// 		assert_noop!(Sudo::sudo(Origin::signed(2), call), Error::<Test>::RequireSudo);
// 		assert_eq!(logger::log(), vec![42i32]); 
// 	});
// }

// #[test]
// fn sudo_emits_events_correctly() {
// 	new_test_ext(1).execute_with(|| {
// 		// Set block number to 1 because events are not emitted on block 0.
// 		System::set_block_number(1);

// 		// Should emit event to indicate success when called with the root `key` and `call` is `Ok`.
// 		let call = Box::new(Call::Logger(LoggerCall::log(42, 1)));
// 		assert_ok!(Sudo::sudo(Origin::signed(1), call));
// 		let expected_event = TestEvent::sudo(RawEvent::Sudid(Ok(())));
// 		assert!(System::events().iter().any(|a| {a.event == expected_event})); 
// 	})
// }

// #[test]
// fn sudo_unchecked_weight_basics() {
// 	new_test_ext(1).execute_with(|| {
// 		// A privileged function should work when `sudo` is passed the root `key` as origin.
// 		let call = Box::new(Call::Logger(LoggerCall::log(42, 1)));
// 		assert_ok!(Sudo::sudo_unchecked_weight(Origin::signed(1), call, 1_000));
// 		assert_eq!(logger::log(), vec![42i32]); 

// 		// A privileged function should not work when called with a non-root `key`.
// 		let call = Box::new(Call::Logger(LoggerCall::log(42, 1)));
// 		assert_noop!(
// 			Sudo::sudo_unchecked_weight(Origin::signed(2), call, 1_000), 
// 			Error::<Test>::RequireSudo,
// 		);
// 		assert_eq!(logger::log(), vec![42i32]); 

// 		// Controls the dispatched weight.
// 		let call = Box::new(Call::Logger(LoggerCall::log(42, 1)));
// 		let sudo_unchecked_weight_call = SudoCall::sudo_unchecked_weight(call, 1_000);
// 		let info = sudo_unchecked_weight_call.get_dispatch_info();
// 		assert_eq!(info.weight, 1_000);
// 	});
// }

// #[test]
// fn sudo_unchecked_weight_emits_events_correctly() {
// 	new_test_ext(1).execute_with(|| {
// 		// Set block number to 1 because events are not emitted on block 0.
// 		System::set_block_number(1);

// 		// Should emit event to indicate success when called with the root `key` and `call` is `Ok`.
// 		let call = Box::new(Call::Logger(LoggerCall::log(42, 1)));
// 		assert_ok!(Sudo::sudo_unchecked_weight(Origin::signed(1), call, 1_000));
// 		let expected_event = TestEvent::sudo(RawEvent::Sudid(Ok(())));
// 		assert!(System::events().iter().any(|a| {a.event == expected_event}));
// 	})
// }

// #[test]
// fn set_key_basics() {
// 	new_test_ext(1).execute_with(|| {	
// 		// A root `key` can change the root `key`
// 		assert_ok!(Sudo::set_key(Origin::signed(1), 2));
// 		assert_eq!(Sudo::key(),  2u64);
// 	});

// 	new_test_ext(1).execute_with(|| {
// 		// A non-root `key` will trigger a `RequireSudo` error and a non-root `key` cannot change the root `key`.
// 		assert_noop!(Sudo::set_key(Origin::signed(2), 3), Error::<Test>::RequireSudo);
// 		assert_eq!(Sudo::key(),  1u64);
// 	});
// }

// #[test]
// fn set_key_emits_events_correctly() {
// 	new_test_ext(1).execute_with(|| {	
// 		// Set block number to 1 because events are not emitted on block 0.
// 		System::set_block_number(1);

// 		// A root `key` can change the root `key`.
// 		assert_ok!(Sudo::set_key(Origin::signed(1), 2));
// 		let expected_event = TestEvent::sudo(RawEvent::KeyChanged(1));
// 		assert!(System::events().iter().any(|a| {a.event == expected_event}));
// 		// Double check.
// 		assert_ok!(Sudo::set_key(Origin::signed(2), 4));
// 		let expected_event = TestEvent::sudo(RawEvent::KeyChanged(2));
// 		assert!(System::events().iter().any(|a| {a.event == expected_event}));
// 	});
// }

#[test]
fn sudo_as_basics() {
	new_test_ext(1).execute_with(|| {
		// I32Log is empty before being used.
		assert_eq!(Logger::i32_log(), vec![]);

		// A privileged function will not work when passed to `sudo_as`.
		let call = Box::new(Call::Logger(LoggerCall::privileged_i32_log(42, 1)));
		assert_ok!(Sudo::sudo_as(Origin::signed(1), 2, call));
		assert_eq!(Logger::i32_log(), vec![]); 

		// A non-privileged function should not work when called with a non-root `key`.
		let call = Box::new(Call::Logger(LoggerCall::non_privileged_i32_log(42, 1)));
		assert_noop!(Sudo::sudo_as(Origin::signed(3), 2, call), Error::<Test>::RequireSudo);
		assert_eq!(Logger::i32_log(), vec![]); 

		// A non-privileged function will work when passed to `sudo_as` with the root `key`.
		let call = Box::new(Call::Logger(LoggerCall::non_privileged_i32_log(42, 1)));
		assert_ok!(Sudo::sudo_as(Origin::signed(1), 2, call));
		assert_eq!(Logger::i32_log(), vec![42i32]);

		// SeenAccounts log is empty before being used
		assert_eq!(Logger::account_log(), vec![]);

		// The correct user makes the call within `sudo_as`.
		let call = Box::new(Call::Logger(LoggerCall::non_privileged_account_log(42, 1_000)));
		assert_ok!(Sudo::sudo_as(Origin::signed(1), 2, call));
		assert_eq!(Logger::account_log(), vec![2]);
	});
}

#[test]
fn sudo_as_emits_events_correctly() {
		new_test_ext(1).execute_with(|| {	
		// Set block number to 1 because events are not emitted on block 0.
		System::set_block_number(1);

		// A non-privileged function will work when passed to `sudo_as` with the root `key`.
		let call = Box::new(Call::Logger(LoggerCall::non_privileged_i32_log(42, 1)));
		assert_ok!(Sudo::sudo_as(Origin::signed(1), 2, call));
		let expected_event = TestEvent::sudo(RawEvent::SudoAsDone(true));
		assert!(System::events().iter().any(|a| {a.event == expected_event}));
	});
}
