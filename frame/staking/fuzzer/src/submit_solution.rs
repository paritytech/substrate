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

use honggfuzz::fuzz;

use mock::Test;
use pallet_staking::testing_utils::{
	USER, get_seq_phragmen_solution, get_weak_solution, setup_chain_stakers,
	set_validator_count, signed_account,
};
use frame_support::{assert_ok, storage::StorageValue};
use sp_runtime::{traits::Dispatchable, DispatchError};
use sp_core::offchain::{testing::TestOffchainExt, OffchainExt};

mod mock;

#[repr(u32)]
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
	/// Initial submission. This will be rather cheap.
	InitialSubmission,
	/// A better submission that will replace the previous ones. This is the most expensive.
	StrongerSubmission,
	/// A weak submission that will be rejected. This will be rather cheap.
	WeakerSubmission,
}

pub fn new_test_ext(iterations: u32) -> sp_io::TestExternalities {
	let mut ext: sp_io::TestExternalities = frame_system::GenesisConfig::default().build_storage::<mock::Test>().map(Into::into)
		.expect("Failed to create test externalities.");

	let (offchain, offchain_state) = TestOffchainExt::new();

	let mut seed = [0u8; 32];
	seed[0..4].copy_from_slice(&iterations.to_le_bytes());
	offchain_state.write().seed = seed;

	ext.register_extension(OffchainExt::new(offchain));

	ext
}

fn main() {
	let to_range = |x: u32, a: u32, b: u32| {
		let collapsed = x % b;
		if collapsed >= a {
			collapsed
		} else {
			collapsed + a
		}
	};
	loop {
		fuzz!(|data: (u32, u32, u32, u32, u32)| {
			let (mut num_validators, mut num_nominators, mut edge_per_voter, mut to_elect, mode_u32) = data;
			let mut ext = new_test_ext(5);
			let mode: Mode = unsafe { std::mem::transmute(mode_u32) };
			num_validators = to_range(num_validators, 50, 1000);
			num_nominators = to_range(num_nominators, 50, 2000);
			edge_per_voter = to_range(edge_per_voter, 1, 16);
			to_elect = to_range(to_elect, 20, num_validators);
			let do_reduce = true;

			println!("+++ instance with params {} / {} / {} / {:?}({}) / {}",
				num_nominators,
				num_validators,
				edge_per_voter,
				mode,
				mode_u32,
				to_elect,
			);

			ext.execute_with(|| {
				// initial setup
				set_validator_count::<Test>(to_elect);
				pallet_staking::testing_utils::init_active_era();
				setup_chain_stakers::<Test>(
					num_validators,
					num_nominators,
					edge_per_voter,
				);
				<pallet_staking::EraElectionStatus<Test>>::put(pallet_staking::ElectionStatus::Open(1));

				println!("++ Chain setup done.");

				// stuff to submit
				let (winners, compact, score) = match mode {
					Mode::InitialSubmission => {
						/* No need to setup anything */
						get_seq_phragmen_solution::<Test>(do_reduce)
					},
					Mode::StrongerSubmission => {
						let (winners, compact, score) = get_weak_solution::<Test>(false);
						println!("Weak on chain score = {:?}", score);
						assert_ok!(
							<pallet_staking::Module<Test>>::submit_election_solution(
								signed_account::<Test>(USER),
								winners,
								compact,
								score,
								pallet_staking::testing_utils::active_era::<Test>(),
							)
						);
						get_seq_phragmen_solution::<Test>(do_reduce)
					},
					Mode::WeakerSubmission => {
						let (winners, compact, score) = get_seq_phragmen_solution::<Test>(do_reduce);
						println!("Strong on chain score = {:?}", score);
						assert_ok!(
							<pallet_staking::Module<Test>>::submit_election_solution(
								signed_account::<Test>(USER),
								winners,
								compact,
								score,
								pallet_staking::testing_utils::active_era::<Test>(),
							)
						);
						get_weak_solution::<Test>(false)
					}
				};

				println!("++ Submission ready. Score = {:?}", score);

				// must have chosen correct number of winners.
				assert_eq!(winners.len() as u32, <pallet_staking::Module<Test>>::validator_count());

				// final call and origin
				let call = pallet_staking::Call::<Test>::submit_election_solution(
					winners,
					compact,
					score,
					pallet_staking::testing_utils::active_era::<Test>(),
				);
				let caller = signed_account::<Test>(USER);

				// actually submit
				match mode {
					Mode::WeakerSubmission => {
						assert_eq!(
							call.dispatch(caller.into()).unwrap_err().error,
							DispatchError::Module { index: 0, error: 16, message: Some("PhragmenWeakSubmission") },
						);
					},
					// NOTE: so exhaustive pattern doesn't work here.. maybe some rust issue? or due to `#[repr(u32)]`?
					Mode::InitialSubmission | Mode::StrongerSubmission => assert!(call.dispatch(caller.into()).is_ok()),
				};
			})
		});
	}
}
