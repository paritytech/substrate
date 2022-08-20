use super::*;
use frame_support::{assert_err, assert_ok};
use mock::{
	active_era, current_era, start_session, Balances, ExtBuilder, Origin, RootOffences, System,
};

#[test]
fn create_offence_fails_given_signed_origin() {
	use sp_runtime::traits::BadOrigin;
	ExtBuilder::default().build_and_execute(|| {
		let offenders = (&[]).to_vec();
		assert_err!(RootOffences::create_offence(Origin::signed(1), offenders), BadOrigin);
	})
}

#[test]
fn create_offence_works_given_root_origin() {
	ExtBuilder::default().build_and_execute(|| {
		start_session(1);

		assert_eq!(active_era(), 0);
		assert_eq!(current_era(), 0);

		assert_eq!(Balances::free_balance(11), 1000);

		let offenders = [(11, Perbill::from_percent(50))].to_vec();
		assert_ok!(RootOffences::create_offence(Origin::root(), offenders.clone()));

		// the slash should be applied, so the unapplied slash is zero.
		System::assert_last_event(Event::CreatedOffence { offenders, unapplied_slash: 0 }.into());
		assert_eq!(Balances::free_balance(11), 500);

		// the other validator should keep his balance, because we only created
		// an offences for the first validator.
		assert_eq!(Balances::free_balance(21), 1000);
	})
}
