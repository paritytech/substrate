use super::*;
use mock::{
	Sudo, Origin, Call, Test, PrivelegedCall, new_test_ext,
}; 
use frame_support::{assert_ok, assert_err};

#[test]
fn new_test_ext_and_sudo_get_key_works() {
	new_test_ext(1).execute_with(|| {
		assert_eq!(Sudo::key(),  1u64);
	});
}

#[test]
fn basic_sudo(){
	new_test_ext(1).execute_with(|| {
		// A privelleged function should work when passed the root_key as origin
		let call = Box::new(Call::Priveleged(PrivelegedCall::privileged_function()));
		assert_ok!(Sudo::sudo(Origin::signed(1), call));
		// A privelleged function should not work when called with a non-root user
		let call = Box::new(Call::Priveleged(PrivelegedCall::privileged_function()));
		assert_err!(
			Sudo::sudo(Origin::signed(2), call), 
			Error::<Test>::RequireSudo,
		);
	});
}
