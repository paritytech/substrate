use frame_support::assert_ok;
use crate::mock::*;

#[test]
fn timestamp_works() {
    new_test_ext().execute_with(|| {
        Timestamp::set_timestamp(42);
        assert_ok!(Timestamp::set(Origin::none(), 69));
        assert_eq!(Timestamp::now(), 69);
    });
}

#[test]
#[should_panic(expected = "Timestamp must be updated only once in the block")]
fn double_timestamp_should_fail() {
    new_test_ext().execute_with(|| {
        Timestamp::set_timestamp(42);
        assert_ok!(Timestamp::set(Origin::none(), 69));
        let _ = Timestamp::set(Origin::none(), 70);
    });
}

#[test]
#[should_panic(
expected = "Timestamp must increment by at least <MinimumPeriod> between sequential blocks"
)]
fn block_period_minimum_enforced() {
    new_test_ext().execute_with(|| {
        Timestamp::set_timestamp(42);
        let _ = Timestamp::set(Origin::none(), 46);
    });
}