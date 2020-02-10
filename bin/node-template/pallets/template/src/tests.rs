// Tests to be written here

use crate::{Error, mock::*};
use frame_support::{assert_ok, assert_noop};

#[test]
fn it_works_for_default_value() {
	new_test_ext().execute_with(|| {
		// Just a dummy test for the dummy funtion `do_something`
		// calling the `do_something` function with a value 42
		assert_ok!(TemplateModule::do_something(Origin::signed(1), 42));
		// asserting that the stored value is equal to what we stored
		assert_eq!(TemplateModule::something(), Some(42));
	});
}

#[test]
fn correct_error_for_none_value() {
	new_test_ext().execute_with(|| {
		// Ensure the correct error is thrown on None value
		assert_noop!(
			TemplateModule::cause_error(Origin::signed(1)),
			Error::<Test>::NoneValue
		);
	});
}
