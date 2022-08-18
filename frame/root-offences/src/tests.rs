use super::*;
use frame_support::{assert_err, assert_ok};
use mock::{new_test_ext, start_session, Origin, RootOffences, Balances};

#[test]
fn create_offence_fails_given_signed_origin() {
	use sp_runtime::traits::BadOrigin;
	new_test_ext().execute_with(|| {
		let offenders = (&[]).to_vec();
		assert_err!(RootOffences::create_offence(Origin::signed(1), offenders), BadOrigin);
	})
}

#[test]
fn create_offence_works_given_root_origin() {
	new_test_ext().execute_with(|| {
		start_session(1);

		assert_eq!(Balances::free_balance(11), 550);
		
		let offenders = [(11, Perbill::from_percent(50))].to_vec();
		assert_ok!(RootOffences::create_offence(Origin::root(), offenders));

		start_session(2);
		assert_eq!(Balances::free_balance(11), 550);
	})
}
