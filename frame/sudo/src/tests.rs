use super::*;
use mock::{
	Sudo, Origin, Call, Test, PrivelegedCall, new_test_ext,
}; 
use frame_support::{assert_ok, assert_err};

#[test]
fn new_test_ext_and_sudo_get_key_works() {
	// test the enivoremnt setup and pallets key retrieval works as expected
	new_test_ext(1).execute_with(|| {
		assert_eq!(Sudo::key(),  1u64);
	});
}

#[test]
fn sudo_basics(){
	new_test_ext(1).execute_with(|| {
		// A privelleged function should work when passed the root_key as origin
		let call = Box::new(Call::Priveleged(PrivelegedCall::privileged_function()));
		assert_ok!(Sudo::sudo(Origin::signed(1), call));
		// A privelleged function should not work when called with a non-root user
		let call = Box::new(Call::Priveleged(PrivelegedCall::privileged_function()));
		assert_err!(Sudo::sudo(Origin::signed(2), call), Error::<Test>::RequireSudo);
	});
}

#[test]
fn sudo_unchecked_weight_basics(){
	new_test_ext(1).execute_with(|| {
		// A privelleged function should work when passed the root_key as origin
		let call = Box::new(Call::Priveleged(PrivelegedCall::privileged_function()));
		// TODO figure out if tests should check varying weights
		assert_ok!(Sudo::sudo_unchecked_weight(Origin::signed(1), call, 1));
		// A privelleged function should not work when called with a non-root user
		let call = Box::new(Call::Priveleged(PrivelegedCall::privileged_function()));
		assert_err!(Sudo::sudo(Origin::signed(2), call), Error::<Test>::RequireSudo);
	});
}

#[test]
fn set_key_basic() {
	new_test_ext(1).execute_with(|| {	
		// A root key can change the root key
		Sudo::set_key(Origin::signed(1), 2);
		assert_eq!(Sudo::key(),  2u64);
	});
	new_test_ext(1).execute_with(|| {	
		// A non root key cannot change the root key
		Sudo::set_key(Origin::signed(2), 3);
		assert_eq!(Sudo::key(),  1u64);
		// A non root key will triggered a require sudo error
		assert_err!(Sudo::set_key(Origin::signed(2), 3), Error::<Test>::RequireSudo);
	});
}