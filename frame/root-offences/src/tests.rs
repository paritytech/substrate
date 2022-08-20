use super::*;
use frame_support::{assert_err, assert_ok};
use mock::{
	active_era, current_era, new_test_ext, start_session, Balances, Origin, RootOffences, System,
};

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
		// NOTE: this test is still WIP.
		start_session(1);
		start_session(2);
		start_session(3);

		assert_eq!(active_era(), 1);
		assert_eq!(current_era(), 1);

		assert_eq!(Balances::free_balance(11), 1000);

		let offenders = [(11, Perbill::from_percent(50))].to_vec();
		assert_ok!(RootOffences::create_offence(Origin::root(), offenders.clone()));

		System::assert_last_event(Event::CreatedOffence { offenders, unapplied_slash: 0 }.into());
	})
}
