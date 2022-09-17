// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![cfg(test)]

use super::*;
use crate::mock::{Call, *};

use frame_support::{bounded_vec, assert_err, assert_noop, assert_ok};
use frame_support::dispatch::Dispatchable;

// GENERAL FAIL/NEGATIVE TESTS ---------------------
#[test]
fn fails_to_filter_tx_pause_pallet() {
	new_test_ext().execute_with(|| {
  assert_noop!(
    TxPause::pause_call(
      Origin::signed(mock::PauseOrigin::get()),
      <TxPause as PalletInfoAccess>::name().as_bytes().to_vec().try_into().expect("TxPause name under MaxNameLen"),
      b"some_reasonably_long_extrinsic_function_name".to_vec().try_into().expect("test bits fit in bounded vec")),
      Error::<Test>::IsUnpausable
    );
	});
}

/// I CANNOT call a pallet of function name with a length of string longer than MaxNameLen, it will yield a runtime error... of what type? 
// #[test]
// fn fails_to_filter_too_long_pallet_name() {
// 	new_test_ext().execute_with(|| {
//     let too_long_name = (0u8..(MaxNameLen::get()+1).try_into().unwrap()).collect::<Vec<_>>();

//     // TODO what error here? It panics as is, perhaps redundant test.
//     assert_noop!(
//       TxPause::pause_call(
//         Origin::signed(mock::PauseOrigin::get()),
//         too_long_name.try_into().expect("TxPause name under MaxNameLen"),
//         b"some_reasonably_long_extrinsic_function_name".to_vec().try_into().expect("test bits fit in bounded vec")),
//         Error::<Test>::IsUnpausable
//       );
// 	});
// }

#[test]
fn fails_to_filter_too_long_pallet_name() {
	new_test_ext().execute_with(|| {
    // let too_long_name = Vec::with_capacity((MaxNameLen::get()+1).try_into().unwrap());
    let too_long_name = (0u8..(MaxNameLen::get()+1).try_into().unwrap()).collect::<Vec<_>>();
    assert_noop!(
      TxPause::pause_call(
        Origin::signed(mock::PauseOrigin::get()),
        too_long_name.try_into().expect("TxPause name under MaxNameLen"),
        b"some_reasonably_long_extrinsic_function_name".to_vec().try_into().expect("test bits fit in bounded vec")),
        Error::<Test>::IsUnpausable
      );
	});
}

// #[test]
// fn fails_to_filter_calls_to_safe_mode_pallet() {
// 	new_test_ext().execute_with(|| {
// 		assert_ok!(SafeMode::enable(Origin::signed(0)));
// 		let enabled_at_block = System::block_number();
// 		let call = Call::Balances(pallet_balances::Call::transfer{dest: 1, value: 1});

// 		assert_err!(call.clone().dispatch(Origin::signed(0)), frame_system::Error::<Test>::CallFiltered);
// 		// TODO ^^^ consider refactor to throw a safe mode error, not generic `CallFiltered`

// 		next_block();
// 		assert_ok!(SafeMode::extend(Origin::signed(0)));
// 		assert_ok!(SafeMode::force_extend(Origin::signed(mock::ExtendOrigin::get())));
// 		assert_err!(call.clone().dispatch(Origin::signed(0)), frame_system::Error::<Test>::CallFiltered);
// 		assert_ok!(SafeMode::force_disable(Origin::signed(mock::DisableOrigin::get())));
// 		assert_ok!(SafeMode::repay_stake(Origin::signed(mock::RepayOrigin::get()), 0, enabled_at_block));

// 		next_block();
// 		assert_ok!(SafeMode::enable(Origin::signed(0)));
// 		assert_err!(call.clone().dispatch(Origin::signed(0)), frame_system::Error::<Test>::CallFiltered);
// 		assert_ok!(SafeMode::force_disable(Origin::signed(mock::DisableOrigin::get())));
// 		assert_ok!(SafeMode::slash_stake(Origin::signed(mock::RepayOrigin::get()), 0, enabled_at_block + 2));
// 	});
// }


// #[test]
// fn fails_to_extend_if_not_enabled() {
// 	new_test_ext().execute_with(|| {
// 		assert_eq!(SafeMode::enabled(), None);
// 		assert_noop!(SafeMode::extend(Origin::signed(2)), Error::<Test>::IsDisabled);
// 	});
// }

// // GENERAL SUCCESS/POSITIVE TESTS ---------------------


// #[test]
// fn can_automatically_disable_after_timeout() {
// 	new_test_ext().execute_with(|| {
// 		let enabled_at_block = System::block_number();
// 		assert_ok!(SafeMode::force_enable(Origin::signed(mock::EnableOrigin::get())));
// 		run_to(mock::EnableDuration::get() + enabled_at_block + 1);
// 		SafeMode::on_initialize(System::block_number());
// 		assert_eq!(SafeMode::enabled(), None);
// 	});
// }

// #[test]
// fn can_filter_balance_calls_when_enabled() {
// 	new_test_ext().execute_with(|| {
// 		let call = Call::Balances(pallet_balances::Call::transfer{dest: 1, value: 1});

// 		assert_ok!(call.clone().dispatch(Origin::signed(0)));
// 		assert_ok!(SafeMode::enable(Origin::signed(0)));
// 		assert_err!(call.clone().dispatch(Origin::signed(0)), frame_system::Error::<Test>::CallFiltered);
// 		// TODO ^^^ consider refactor to throw a safe mode error, not generic `CallFiltered`
// 	});
// }

// // SIGNED ORIGIN CALL TESTS ---------------------

// #[test]
// fn can_enable_with_signed_origin() {
// 	new_test_ext().execute_with(|| {
// 		assert_ok!(SafeMode::enable(Origin::signed(0)));
// 		assert_eq!(
// 			SafeMode::enabled().unwrap(),
// 			System::block_number() + mock::EnableDuration::get()
// 		);
// 		assert_eq!(Balances::reserved_balance(0), mock::EnableStakeAmount::get());
// 		assert_noop!(SafeMode::enable(Origin::signed(0)), Error::<Test>::IsEnabled);
// 		// Assert the stake.
// 		assert_eq!(Stakes::<Test>::get(0, 1), Some(mock::EnableStakeAmount::get()));
// 	});
// }

// #[test]
// fn can_extend_with_signed_origin() {
// 	new_test_ext().execute_with(|| {
// 		assert_ok!(SafeMode::enable(Origin::signed(0)));
// 		assert_ok!(SafeMode::extend(Origin::signed(0)));
// 		assert_eq!(
// 			SafeMode::enabled().unwrap(),
// 			System::block_number() + mock::EnableDuration::get() + mock::ExtendDuration::get()
// 		);
// 		assert_eq!(Balances::reserved_balance(0), mock::EnableStakeAmount::get() + mock::ExtendStakeAmount::get());
// 	});
// }

// #[test]
// fn fails_signed_origin_when_explicit_origin_required() {
// 	new_test_ext().execute_with(|| {
// 		assert_eq!(SafeMode::enabled(), None);
// 		let enabled_at_block = System::block_number();

// 		assert_err!(SafeMode::force_enable(Origin::signed(0)), DispatchError::BadOrigin);
// 		assert_err!(SafeMode::force_extend(Origin::signed(0)), DispatchError::BadOrigin);
// 		assert_err!(SafeMode::force_disable(Origin::signed(0)), DispatchError::BadOrigin);
// 		assert_err!(SafeMode::slash_stake(Origin::signed(0), 0, enabled_at_block), DispatchError::BadOrigin);
// 		assert_err!(SafeMode::repay_stake(Origin::signed(0), 0, enabled_at_block), DispatchError::BadOrigin);

// 	});
// }

// // CONFIGURED ORIGIN CALL TESTS ---------------------

// #[test]
// fn fails_force_disable_if_not_enabled() {
// 	new_test_ext().execute_with(|| {
// 		assert_noop!(SafeMode::force_disable(Origin::signed(mock::DisableOrigin::get())), Error::<Test>::IsDisabled);
// 		assert_noop!(
// 			SafeMode::force_disable(Origin::signed(mock::DisableOrigin::get())),
// 			Error::<Test>::IsDisabled
// 		);
// 	});
// }

// #[test]
// fn can_force_enable_with_config_origin() {
// 	new_test_ext().execute_with(|| {
// 		assert_ok!(SafeMode::force_enable(Origin::signed(mock::EnableOrigin::get())));
// 		assert_eq!(
// 			SafeMode::enabled().unwrap(),
// 			System::block_number() + mock::EnableDuration::get()
// 		);
// 		assert_noop!(
// 			SafeMode::force_enable(Origin::signed(mock::EnableOrigin::get())),
// 			Error::<Test>::IsEnabled
// 		);
// 		assert_eq!(Balances::reserved_balance(mock::EnableOrigin::get()), 0);
// 	});
// }

// #[test]
// fn can_force_disable_with_config_origin() {
// 	new_test_ext().execute_with(|| {
// 		assert_eq!(SafeMode::enabled(), None);
// 		assert_err!(
// 			SafeMode::force_disable(Origin::signed(mock::DisableOrigin::get())),
// 			Error::<Test>::IsDisabled
// 		);
// 		assert_ok!(SafeMode::force_enable(Origin::signed(mock::EnableOrigin::get())));
// 		assert_eq!(Balances::reserved_balance(mock::EnableOrigin::get()), 0);
// 		assert_ok!(SafeMode::force_disable(Origin::signed(mock::DisableOrigin::get())));
// 	});
// }

// #[test]
// fn can_force_extend_with_config_origin() {
// 	new_test_ext().execute_with(|| {
// 		assert_ok!(SafeMode::force_enable(Origin::signed(mock::EnableOrigin::get())));
// 		assert_eq!(
// 			SafeMode::enabled().unwrap(),
// 			System::block_number() + mock::EnableDuration::get()
// 		);
// 		assert_ok!(SafeMode::force_extend(Origin::signed(mock::ExtendOrigin::get())));
// 		assert_eq!(
// 			SafeMode::enabled().unwrap(),
// 			System::block_number() + mock::EnableDuration::get() + mock::ExtendDuration::get()
// 		);
// 		assert_eq!(Balances::reserved_balance(mock::EnableOrigin::get()), 0);
// 		assert_eq!(Balances::reserved_balance(mock::ExtendDuration::get()), 0);
// 	});
// }

// #[test]
// fn can_repay_stake_with_config_origin() {
// 	new_test_ext().execute_with(|| {
// 		let enabled_at_block = System::block_number();
// 		assert_ok!(SafeMode::enable(Origin::signed(0)));
// 		assert_err!(
// 			SafeMode::repay_stake(Origin::signed(mock::RepayOrigin::get()), 0, enabled_at_block),
// 			Error::<Test>::IsEnabled
// 		);
// 		run_to(mock::EnableDuration::get() + enabled_at_block + 1);
// 		SafeMode::on_initialize(System::block_number());
// 		assert_ok!(SafeMode::repay_stake(Origin::signed(mock::RepayOrigin::get()), 0, enabled_at_block));
// 		// TODO: test accounting is correct
// 	});
// }

// #[test]
// fn can_slash_stake_with_config_origin() {
// 	new_test_ext().execute_with(|| {
// 		let enabled_at_block = System::block_number();
// 		assert_ok!(SafeMode::enable(Origin::signed(0)));
// 		assert_err!(
// 			SafeMode::slash_stake(Origin::signed(mock::RepayOrigin::get()), 0, enabled_at_block),
// 			Error::<Test>::IsEnabled
// 		);
// 		run_to(mock::EnableDuration::get() + enabled_at_block + 1);
// 		SafeMode::on_initialize(System::block_number());
// 		assert_ok!(SafeMode::slash_stake(Origin::signed(mock::RepayOrigin::get()), 0, enabled_at_block));
// 		// TODO: test accounting is correct
// 	});
// }

// #[test]
// fn fails_when_explicit_origin_required() {
// 	new_test_ext().execute_with(|| {
// 		assert_eq!(SafeMode::enabled(), None);
// 		let enabled_at_block = System::block_number();
		
// 		assert_err!(SafeMode::force_extend(Origin::signed(mock::EnableOrigin::get())), DispatchError::BadOrigin);
// 		assert_err!(SafeMode::force_disable(Origin::signed(mock::EnableOrigin::get())), DispatchError::BadOrigin);
// 		assert_err!(SafeMode::slash_stake(Origin::signed(mock::EnableOrigin::get()), 0, enabled_at_block), DispatchError::BadOrigin);
// 		assert_err!(SafeMode::repay_stake(Origin::signed(mock::EnableOrigin::get()), 0, enabled_at_block), DispatchError::BadOrigin);

// 		assert_err!(SafeMode::force_enable(Origin::signed(mock::ExtendOrigin::get())), DispatchError::BadOrigin);
// 		assert_err!(SafeMode::force_disable(Origin::signed(mock::ExtendOrigin::get())), DispatchError::BadOrigin);
// 		assert_err!(SafeMode::slash_stake(Origin::signed(mock::ExtendOrigin::get()), 0, enabled_at_block), DispatchError::BadOrigin);
// 		assert_err!(SafeMode::repay_stake(Origin::signed(mock::ExtendOrigin::get()), 0, enabled_at_block), DispatchError::BadOrigin);

// 		assert_err!(SafeMode::force_enable(Origin::signed(mock::DisableOrigin::get())), DispatchError::BadOrigin);
// 		assert_err!(SafeMode::force_extend(Origin::signed(mock::DisableOrigin::get())), DispatchError::BadOrigin);
// 		assert_err!(SafeMode::slash_stake(Origin::signed(mock::DisableOrigin::get()), 0, enabled_at_block), DispatchError::BadOrigin);
// 		assert_err!(SafeMode::repay_stake(Origin::signed(mock::DisableOrigin::get()), 0, enabled_at_block), DispatchError::BadOrigin);

// 		assert_err!(SafeMode::force_enable(Origin::signed(mock::RepayOrigin::get())), DispatchError::BadOrigin);
// 		assert_err!(SafeMode::force_extend(Origin::signed(mock::RepayOrigin::get())), DispatchError::BadOrigin);
// 		assert_err!(SafeMode::force_disable(Origin::signed(mock::RepayOrigin::get())), DispatchError::BadOrigin);

// 	});
// }

