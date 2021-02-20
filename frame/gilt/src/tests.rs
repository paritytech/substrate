use crate::{Error, mock::*};
use frame_support::{assert_ok, assert_noop};

#[test]
fn it_works_for_default_value() {
	new_test_ext().execute_with(|| {
	});
}

#[test]
fn correct_error_for_none_value() {
	new_test_ext().execute_with(|| {
	});
}
