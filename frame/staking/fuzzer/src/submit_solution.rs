// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Fuzzing for staking pallet.
//!
//! # Running
//!
//! Run with `cargo hfuzz run submit_solution`. `honggfuzz`.
//!
//! # Debugging a panic
//!
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug submit_solution hfuzz_workspace/reduce/*.fuzz`.

use honggfuzz::fuzz;

use mock::Test;
use pallet_staking::testing_utils::{
	self, USER, get_seq_phragmen_solution, get_weak_solution, setup_chain_stakers,
	set_validator_count, signed_account,
};
use frame_support::assert_ok;
use sp_runtime::{traits::Dispatchable, DispatchError};

mod mock;

#[repr(u32)]
#[allow(dead_code)]
#[derive(Debug, Clone, Copy)]
enum Mode {
	/// Initial submission. This will be rather cheap
	InitialSubmission,
	/// A better submission that will replace the previous ones. This is the most expensive.
	StrongerSubmission,
	/// A weak submission that will be rejected. This will be rather cheap.
	WeakerSubmission,
}

fn main() {
	loop {
		fuzz!(|_data: _| {
			let mut ext = mock::new_test_ext();
			let mode: Mode = unsafe { std::mem::transmute(testing_utils::random(0, 2)) };
			let num_validators = testing_utils::random(100, 1000);
			let num_nominators = testing_utils::random(100, 20_000);
			let edge_per_voter = 16;
			let do_reduce = true;
			let to_elect = testing_utils::random(100, num_validators);

			println!("++ instance with params {} / {} / {} / {:?} / {}",
				num_nominators,
				num_validators,
				edge_per_voter,
				mode,
				to_elect,
			);

			ext.execute_with(|| {
				// initial setup
				set_validator_count::<Test>(to_elect);
				setup_chain_stakers::<Test>(
					num_validators,
					num_nominators,
					edge_per_voter,
				);

				// stuff to submit
				let (winners, compact, score) = match mode {
					Mode::InitialSubmission => {
						/* No need to setup anything */
						get_seq_phragmen_solution::<Test>(do_reduce)
					},
					Mode::StrongerSubmission => {
						let (winners, compact, score) = get_weak_solution::<Test>(false);
						assert_ok!(
							<pallet_staking::Module<Test>>::submit_election_solution(
								signed_account::<Test>(USER),
								winners,
								compact,
								score,
							)
						);
						get_seq_phragmen_solution::<Test>(do_reduce)
					},
					Mode::WeakerSubmission => {
						let (winners, compact, score) = get_seq_phragmen_solution::<Test>(do_reduce);
						assert_ok!(
							<pallet_staking::Module<Test>>::submit_election_solution(
								signed_account::<Test>(USER),
								winners,
								compact,
								score,
							)
						);
						get_weak_solution::<Test>(false)
					}
				};

				// must have chosen correct number of winners.
				assert_eq!(winners.len() as u32, <pallet_staking::Module<Test>>::validator_count());

				let call = pallet_staking::Call::<Test>::submit_election_solution(
					winners,
					compact,
					score,
				);
				let caller = signed_account::<Test>(USER);

				// actually submit
				match mode {
					Mode::WeakerSubmission => {
						assert_eq!(
							call.dispatch(caller.into()).unwrap_err(),
							DispatchError::Module { index: 0, error: 11, message: Some("PhragmenWeakSubmission") },
						);
					},
					_ => assert_ok!(call.dispatch(caller.into())),
				};
			})
	 	});
	}
}
