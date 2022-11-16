use crate::{mock::*, Error};
use frame_support::{assert_noop, assert_ok, traits::Currency};

#[test]
fn address_is_set() {
	new_test_ext().execute_with(|| {
		// Dispatch a signed extrinsic.
		assert_eq!(NftFractions::pallet_address(), None);
		assert_ok!(NftFractions::set_pallet_address(RuntimeOrigin::signed(1)));
		assert_eq!(NftFractions::pallet_address(), Some(1u64));
		// assert_eq!(
		// 	NftFractions::issuance(),
		// 	Some(<Balances as Currency<_>>::total_issuance())
		// )
	});
}
