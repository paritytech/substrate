use super::*;
use mock::{ Sudo, SudoCall, Origin, Call, Test, new_test_ext, logger, LoggerCall,
TestEvent, System }; 
use frame_support::{assert_ok, assert_noop};

#[test]
fn new_test_ext_and_sudo_get_key_works() {
	// Test that the enivroment setup and pallets `key` retrieval works as expected.
	new_test_ext(1).execute_with(|| {
		assert_eq!(Sudo::key(),  1u64);
	});
}

#[test]
fn sudo_basics() {
	new_test_ext(1).execute_with(|| {
		// A priveleged function should work when `sudo` is passed the root_key as origin.
		let call = Box::new(Call::Logger(LoggerCall::log(42, 1)));
		assert_ok!(Sudo::sudo(Origin::signed(1), call));
		assert_eq!(logger::log(), vec![42u64]); 
		
		// A priveleged function should not work when `sudo` is called with a non-root key.
		let call = Box::new(Call::Logger(LoggerCall::log(42, 1)));
		assert_noop!(Sudo::sudo(Origin::signed(2), call), Error::<Test>::RequireSudo);
		assert_eq!(logger::log(), vec![42u64]); 
	});
}

#[test]
fn sudo_emits_events_correctly() {
	new_test_ext(1).execute_with(|| {
		// Set block number to 1 because events are not emitted on block 0.
		System::set_block_number(1);

		// Should emit event to indicate succes when called with the `root_key` and `call` is `Ok`.
		let call = Box::new(Call::Logger(LoggerCall::log(42, 1)));
		assert_ok!(Sudo::sudo(Origin::signed(1), call));
		let expected_event = TestEvent::sudo(RawEvent::Sudid(Ok(())));
		assert!(System::events().iter().any(|a| {a.event == expected_event})); 
	})
}

#[test]
fn sudo_unchecked_weight_basics() {
	new_test_ext(1).execute_with(|| {
		// A priveleged function should work when `sudo` is passed the `root_key` as origin.
		let call = Box::new(Call::Logger(LoggerCall::log(42, 1)));
		assert_ok!(Sudo::sudo_unchecked_weight(Origin::signed(1), call, 1_000));
		assert_eq!(logger::log(), vec![42u64]); 

		// A priveleged function should not work when called with a non-root key.
		let call = Box::new(Call::Logger(LoggerCall::log(42, 1)));
		assert_noop!(
			Sudo::sudo_unchecked_weight(Origin::signed(2), call, 1_000), 
			Error::<Test>::RequireSudo,
		);
		assert_eq!(logger::log(), vec![42u64]); 

		// Controlls the dispatched weight.
		let call = Box::new(Call::Logger(LoggerCall::log(42, 1)));
		let sudo_unchecked_weight_call = SudoCall::sudo_unchecked_weight( call, 1_000);
		let info = sudo_unchecked_weight_call.get_dispatch_info();
		assert_eq!(info.weight, 1_000);
	});
}

#[test]
fn sudo_unchecked_weight_emits_events_correctly() {
	new_test_ext(1).execute_with(|| {
		// Set block number to 1 because events are not emitted on block 0.
		System::set_block_number(1);

		// Should emit event to indicate succes when called with the `root_key` and `call` is `Ok`.
		let call = Box::new(Call::Logger(LoggerCall::log(42, 1)));
		assert_ok!(Sudo::sudo_unchecked_weight(Origin::signed(1), call, 1_000));
		let expected_event = TestEvent::sudo(RawEvent::Sudid(Ok(())));
		assert!(System::events().iter().any(|a| {a.event == expected_event}));
	})
}

#[test]
fn set_key_basics() {
	new_test_ext(1).execute_with(|| {	
		// A `root_key` can change the `root_key`
		assert_ok!(Sudo::set_key(Origin::signed(1), 2));
		assert_eq!(Sudo::key(),  2u64);
	});

	new_test_ext(1).execute_with(|| {
		// A non `root_key` will trigger a `RequireSudo` error and a non-root key cannot change the `root_key`.
		assert_noop!(Sudo::set_key(Origin::signed(2), 3), Error::<Test>::RequireSudo);
		assert_eq!(Sudo::key(),  1u64);
	});
}

#[test]
fn set_key_emits_events_correctly() {
	new_test_ext(1).execute_with(|| {	
		// Set block number to 1 because events are not emitted on block 0.
		System::set_block_number(1);

		// A `root_key` can change the `root_key`.
		assert_ok!(Sudo::set_key(Origin::signed(1), 2));
		let expected_event = TestEvent::sudo(RawEvent::KeyChanged(1));
		assert!(System::events().iter().any(|a| {a.event == expected_event}));

		assert_ok!(Sudo::set_key(Origin::signed(2), 4));
		let expected_event = TestEvent::sudo(RawEvent::KeyChanged(2));
		assert!(System::events().iter().any(|a| {a.event == expected_event}));
	});
}

#[test]
fn sudo_as_basics() {
	new_test_ext(1).execute_with(|| {	
		// A priveleged function will not work when passed to `sudo_as`
		let call = Box::new(Call::Logger(LoggerCall::log(42, 1)));
		assert_ok!(Sudo::sudo_as(Origin::signed(1), 2, call));
		assert_eq!(logger::log(), vec![]); 

		// A non-priveleged function should not work when called with a non-root key.
		let call = Box::new(Call::Logger(LoggerCall::non_priveleged_log(42, 1)));
		assert_noop!(Sudo::sudo_as(Origin::signed(3), 2, call), Error::<Test>::RequireSudo);
		assert_eq!(logger::log(), vec![]); 

		// A non-priveleged function will work when passed to `sudo_as` with the `root_key`.
		let call = Box::new(Call::Logger(LoggerCall::non_priveleged_log(42, 1)));
		assert_ok!(Sudo::sudo_as(Origin::signed(1), 2, call));
		assert_eq!(logger::log(), vec![42u64]); 
	});
}

#[test]
fn sudo_as_emits_events_correctly() {
		new_test_ext(1).execute_with(|| {	
		// Set block number to 1 because events are not emitted on block 0.
		System::set_block_number(1);

		// A non-priveleged function will work when passed to `sudo_as` with the `root_key`.
		let call = Box::new(Call::Logger(LoggerCall::non_priveleged_log(42, 1)));
		assert_ok!(Sudo::sudo_as(Origin::signed(1), 2, call));
		let expected_event = TestEvent::sudo(RawEvent::SudoAsDone(true));
		assert!(System::events().iter().any(|a| {a.event == expected_event}));
	});
}
