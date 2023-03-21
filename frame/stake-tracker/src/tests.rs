// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
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

use super::mock::*;
use crate as pallet_stake_tracker;
use frame_election_provider_support::SortedListProvider;

use crate::ApprovalStake;
use frame_support::{
	assert_err, assert_ok, assert_storage_noop,
	traits::fungible::{Inspect, Mutate, Unbalanced},
};
use sp_staking::{OnStakingUpdate, StakingInterface};

pub(crate) type VoterList = <Runtime as pallet_stake_tracker::Config>::VoterList;
pub(crate) type TargetList = <Runtime as pallet_stake_tracker::Config>::TargetList;

// Note that the total stake is ignored in the implementation, so we just keep it at 0 for
// convenience.
mod on_stake_update {
	use super::*;
	use frame_support::traits::tokens::Precision::Exact;

	#[test]
	#[should_panic(expected = "on_stake_update is called on a bonded account; qed")]
	fn defensive_when_not_bonded() {
		ExtBuilder::default().build_and_execute(|| {
			// user without stake
			assert_storage_noop!(StakeTracker::on_stake_update(&30, None));
		});
	}

	#[test]
	fn validator_works() {
		ExtBuilder::default().build_and_execute(|| {
			let validator_id = 10;

			StakeTracker::on_validator_add(&validator_id);
			assert_eq!(
				VoterList::get_score(&validator_id).unwrap(),
				StakeTracker::to_vote(StakeTracker::active_stake_of(&validator_id))
			);
			assert_eq!(
				TargetList::get_score(&validator_id).unwrap(),
				StakeTracker::active_stake_of(&validator_id)
			);
			assert_eq!(
				StakeTracker::approval_stake(&validator_id).unwrap(),
				StakeTracker::active_stake_of(&validator_id)
			);
			let mut prev_stake = Staking::stake(&validator_id).unwrap();

			// test stake update logic
			for balance in vec![
				// same
				Balances::balance(&validator_id),
				// lower
				Balances::balance(&validator_id) - 2,
				// higher
				Balances::balance(&validator_id) + 2,
			] {
				Balances::set_balance(&validator_id, balance);

				StakeTracker::on_stake_update(&validator_id, Some(prev_stake.clone()));
				assert_eq!(
					VoterList::get_score(&validator_id).unwrap(),
					StakeTracker::to_vote(StakeTracker::active_stake_of(&validator_id))
				);
				assert_eq!(
					TargetList::get_score(&validator_id).unwrap(),
					StakeTracker::active_stake_of(&validator_id)
				);
				assert_eq!(
					StakeTracker::approval_stake(&validator_id).unwrap(),
					StakeTracker::active_stake_of(&validator_id)
				);
				prev_stake = Staking::stake(&validator_id).unwrap();
			}
		});
	}

	#[test]
	fn nominator_works() {
		ExtBuilder::default().build_and_execute(|| {
			let nominator_id = 20;
			let nominations = Staking::nominations(&nominator_id).unwrap();

			StakeTracker::on_nominator_add(&nominator_id);

			let mut prev_stake = Staking::stake(&nominator_id).unwrap();

			for validator in &nominations {
				StakeTracker::on_validator_add(validator);
			}

			// test stake update logic
			for balance in vec![
				// same
				Balances::balance(&nominator_id),
				// lower
				Balances::balance(&nominator_id) - 2,
				// higher
				Balances::balance(&nominator_id) + 2,
			] {
				Balances::set_balance(&nominator_id, balance);

				let nominator_stake = StakeTracker::active_stake_of(&nominator_id);

				StakeTracker::on_stake_update(&nominator_id, Some(prev_stake.clone()));
				assert_eq!(
					VoterList::get_score(&nominator_id).unwrap(),
					StakeTracker::to_vote(nominator_stake)
				);

				for validator in &nominations {
					let validator_stake = StakeTracker::active_stake_of(validator);
					assert_eq!(
						TargetList::get_score(validator).unwrap(),
						validator_stake + nominator_stake
					);
					assert_eq!(
						StakeTracker::approval_stake(validator).unwrap(),
						validator_stake + nominator_stake
					);
				}

				assert_eq!(TargetList::count(), nominations.len() as u32);

				prev_stake = Staking::stake(&nominator_id).unwrap();
			}

			// test that this works even if validators are not in the TargetList

			for validator in &nominations {
				StakeTracker::on_validator_remove(validator);
			}

			assert_eq!(TargetList::count(), 0);

			assert_ok!(Balances::increase_balance(&nominator_id, 10, Exact));

			StakeTracker::on_stake_update(&nominator_id, Some(prev_stake.clone()));
			assert_eq!(
				VoterList::get_score(&nominator_id).unwrap(),
				StakeTracker::to_vote(StakeTracker::active_stake_of(&nominator_id))
			);

			for validator in &nominations {
				assert_eq!(
					StakeTracker::approval_stake(validator).unwrap(),
					StakeTracker::active_stake_of(&nominator_id)
				);
			}

			assert_eq!(TargetList::count(), 0);
		});
	}

	#[test]
	#[should_panic(expected = "Nominator's position in VoterList updated; qed")]
	fn defensive_when_not_in_list_nominator() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			StakeTracker::on_stake_update(&20, None);
		});
	}

	#[test]
	#[should_panic(expected = "Validator's position in VoterList updated; qed")]
	fn defensive_when_not_in_voter_list_validator() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			assert_ok!(TargetList::on_insert(10, 1));
			StakeTracker::on_stake_update(&10, None);
		});
	}

	#[test]
	#[should_panic(expected = "Validator exists in TargetList; qed.")]
	fn defensive_when_not_in_target_list_validator() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			StakeTracker::on_stake_update(&10, None);
		});
	}
}

mod on_nominator_add {
	use super::*;

	#[test]
	fn works_with_empty_lists() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			assert_eq!(TargetList::count(), 0);

			let nominations = nominations();

			for id in Nominators::get() {
				StakeTracker::on_nominator_add(&id);
				assert_eq!(
					VoterList::get_score(&id).unwrap(),
					StakeTracker::to_vote(StakeTracker::active_stake_of(&id))
				);
			}

			for (nomination, score) in nominations.clone() {
				assert_eq!(StakeTracker::approval_stake(&nomination).unwrap_or_default(), score);
			}

			assert_eq!(VoterList::count(), Nominators::get().len() as u32);
			// does not update the TargetList as the validators were not added to it
			assert_eq!(TargetList::count(), 0);
		});
	}

	#[test]
	fn works_with_prepopulated_target_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			assert_eq!(TargetList::count(), 0);

			let nominations = nominations();

			// prepopulate the TargetList with nominated validators
			for (nomination, _) in &nominations {
				StakeTracker::on_validator_add(&nomination);
			}

			// nominators
			for id in Nominators::get() {
				StakeTracker::on_nominator_add(&id);
				assert_eq!(
					VoterList::get_score(&id).unwrap(),
					StakeTracker::to_vote(StakeTracker::active_stake_of(&id))
				);
			}

			for (nomination, score) in &nominations {
				let approval_stake = *score + StakeTracker::active_stake_of(nomination);
				assert_eq!(
					StakeTracker::approval_stake(nomination).unwrap_or_default(),
					approval_stake
				);
				assert_eq!(
					StakeTracker::approval_stake(nomination).unwrap_or_default(),
					TargetList::get_score(nomination).unwrap()
				);
			}

			assert_eq!(VoterList::count(), (Nominators::get().len() + nominations.len()) as u32);
			assert_eq!(TargetList::count(), nominations.len() as u32);
		});
	}

	#[test]
	#[should_panic(expected = "Nominator inserted into VoterList; qed")]
	fn defensive_when_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			StakeTracker::on_nominator_add(&20);
			StakeTracker::on_nominator_add(&20);
		});
	}

	#[test]
	#[should_panic(expected = "on_nominator_add is called for a nominator; qed")]
	fn defensive_works_only_for_nominators() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			StakeTracker::on_nominator_add(&10);
		});
	}
}

mod on_nominator_update {
	use super::*;

	#[test]
	fn noop_for_empty_nominations() {
		ExtBuilder::default().build_and_execute(|| {
			// nominators with no nominations
			for id in Nominators::get()
				.iter()
				.filter(|id| Staking::nominations(&id).unwrap().len() == 0)
			{
				StakeTracker::on_nominator_add(&id);
				assert_storage_noop!(StakeTracker::on_nominator_update(&id, Vec::new()));
			}
		});
	}

	#[test]
	#[should_panic(expected = "Active nominator is in the VoterList; qed")]
	fn defensive_not_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			StakeTracker::on_nominator_update(&20, Vec::new())
		});
	}

	#[test]
	fn nomination_scenarios() {
		ExtBuilder::default().build_and_execute(|| {
			let nominator_id = 20;
			StakeTracker::on_nominator_add(&nominator_id);

			// nominations are not in TargetList
			StakeTracker::on_nominator_update(
				&nominator_id,
				Staking::nominations(&nominator_id).unwrap(),
			);

			for nomination in Staking::nominations(&nominator_id).unwrap() {
				assert_err!(
					TargetList::get_score(&nomination),
					pallet_bags_list::ListError::NodeNotFound
				);
				assert_eq!(
					StakeTracker::approval_stake(&nomination).unwrap(),
					StakeTracker::active_stake_of(&nominator_id)
				);
			}

			assert_eq!(ApprovalStake::<Runtime>::count(), 2);
			let _ = ApprovalStake::<Runtime>::clear(100, None);

			// no prev nominations and nominations are in TargetList
			for nomination in Staking::nominations(&nominator_id).unwrap() {
				let _ = StakeTracker::on_validator_add(&nomination);
			}

			StakeTracker::on_nominator_update(&nominator_id, Vec::new());

			for nomination in Staking::nominations(&nominator_id).unwrap() {
				assert_eq!(
					TargetList::get_score(&nomination).unwrap(),
					StakeTracker::active_stake_of(&nominator_id)
						.saturating_add(StakeTracker::active_stake_of(&nomination))
				);
				assert_eq!(
					StakeTracker::approval_stake(&nomination).unwrap(),
					StakeTracker::active_stake_of(&nominator_id)
						.saturating_add(StakeTracker::active_stake_of(&nomination))
				);
			}

			// some previous nominations

			// reset two validators to have something new to nominate and something that won't
			// be touched
			for nomination in vec![10, 11] {
				StakeTracker::on_validator_remove(&nomination);
				StakeTracker::on_unstake(&nomination);
				StakeTracker::on_validator_add(&nomination);
			}

			// add a validator to have something to de-nominate
			StakeTracker::on_validator_add(&12);
			StakeTracker::on_nominator_update(&nominator_id, vec![11, 12]);

			assert_eq!(
				TargetList::get_score(&12).unwrap(),
				StakeTracker::active_stake_of(&12)
					.saturating_sub(StakeTracker::active_stake_of(&nominator_id))
			);
			assert_eq!(
				StakeTracker::approval_stake(&12).unwrap(),
				StakeTracker::active_stake_of(&12)
					.saturating_sub(StakeTracker::active_stake_of(&nominator_id))
			);

			assert_eq!(
				TargetList::get_score(&10).unwrap(),
				StakeTracker::active_stake_of(&nominator_id)
					.saturating_add(StakeTracker::active_stake_of(&10))
			);
			assert_eq!(
				StakeTracker::approval_stake(&10).unwrap(),
				StakeTracker::active_stake_of(&nominator_id)
					.saturating_add(StakeTracker::active_stake_of(&10))
			);

			// this is untouched as it was present in both current and prev nominations
			assert_eq!(TargetList::get_score(&11).unwrap(), StakeTracker::active_stake_of(&11));
			assert_eq!(
				StakeTracker::approval_stake(&11).unwrap(),
				StakeTracker::active_stake_of(&11)
			);
		});
	}
}

mod on_validator_add {
	use super::*;

	#[test]
	fn works() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			assert_eq!(TargetList::count(), 0);

			for id in Validators::get() {
				StakeTracker::on_validator_add(&id);
				assert_eq!(
					VoterList::get_score(&id).unwrap(),
					StakeTracker::to_vote(StakeTracker::active_stake_of(&id))
				);
				assert_eq!(
					TargetList::get_score(&id).unwrap(),
					StakeTracker::approval_stake(&id).unwrap()
				);
			}

			assert_eq!(VoterList::count(), Validators::get().len() as u32);
			assert_eq!(TargetList::count(), Validators::get().len() as u32);
		});
	}

	#[test]
	fn works_with_existing_approval_stake() {
		ExtBuilder::default().build_and_execute(|| {
			let nominator_id = 20;

			assert_eq!(VoterList::count(), 0);
			assert_eq!(TargetList::count(), 0);

			StakeTracker::on_nominator_add(&nominator_id);

			// validators
			for id in Staking::nominations(&nominator_id).unwrap() {
				StakeTracker::on_validator_add(&id);
				assert_eq!(
					VoterList::get_score(&id).unwrap(),
					StakeTracker::to_vote(StakeTracker::active_stake_of(&id))
				);
				assert_eq!(
					TargetList::get_score(&id).unwrap(),
					StakeTracker::approval_stake(&id).unwrap()
				);
				assert_eq!(
					StakeTracker::approval_stake(&id).unwrap(),
					StakeTracker::active_stake_of(&id) +
						StakeTracker::active_stake_of(&nominator_id),
				);
			}

			// nominations + nominator
			assert_eq!(
				VoterList::count(),
				(Staking::nominations(&nominator_id).unwrap().len() + 1) as u32
			);

			// validators
			assert_eq!(
				TargetList::count(),
				Staking::nominations(&nominator_id).unwrap().len() as u32
			);
		});
	}

	#[test]
	#[should_panic(expected = "Validator inserted into VoterList; qed")]
	fn defensive_when_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			let id = 10;
			assert_eq!(VoterList::count(), 0);
			let _ = VoterList::on_insert(10, 100);
			StakeTracker::on_validator_add(&id);
		});
	}

	#[test]
	#[should_panic(expected = "Validator inserted into TargetList; qed")]
	fn defensive_when_in_target_list() {
		ExtBuilder::default().build_and_execute(|| {
			let id = 10;
			assert_eq!(TargetList::count(), 0);
			let _ = TargetList::on_insert(id, 100);
			StakeTracker::on_validator_add(&id);
		});
	}
}

mod on_validator_update {
	use super::*;

	#[test]
	fn noop() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			let id = 10;

			StakeTracker::on_validator_add(&id);
			assert_storage_noop!(StakeTracker::on_validator_update(&id));
			assert_eq!(VoterList::count(), 1);
		});
	}

	#[test]
	#[should_panic(expected = "Active validator is in the VoterList; qed")]
	fn defensive_not_in_voter_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			StakeTracker::on_validator_update(&10)
		});
	}

	#[test]
	#[should_panic(expected = "Active validator is in the TargetList; qed")]
	fn defensive_not_in_target_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_ok!(VoterList::on_insert(10, 10));
			assert_eq!(TargetList::count(), 0);
			StakeTracker::on_validator_update(&10)
		});
	}
}

mod on_validator_remove {
	use super::*;

	#[test]
	fn works() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			assert_eq!(TargetList::count(), 0);

			let validator_id = 10;
			let nominator_id = 20;

			StakeTracker::on_validator_add(&validator_id);
			assert_eq!(VoterList::count(), 1);
			assert_eq!(TargetList::count(), 1);
			assert_eq!(
				StakeTracker::approval_stake(&validator_id).unwrap(),
				TargetList::get_score(&validator_id).unwrap()
			);
			assert_eq!(
				StakeTracker::approval_stake(&validator_id).unwrap(),
				StakeTracker::active_stake_of(&validator_id)
			);
			StakeTracker::on_validator_remove(&validator_id);
			assert_eq!(StakeTracker::approval_stake(&validator_id).unwrap(), 0);
			assert_eq!(VoterList::count(), 0);
			assert_eq!(TargetList::count(), 0);

			// with a nomination

			StakeTracker::on_nominator_add(&nominator_id);

			for validator_id in Staking::nominations(&nominator_id).unwrap() {
				StakeTracker::on_validator_add(&validator_id);
				assert_eq!(VoterList::count(), 2);
				assert_eq!(TargetList::count(), 1);
				assert_eq!(
					StakeTracker::approval_stake(&validator_id).unwrap(),
					TargetList::get_score(&validator_id).unwrap()
				);
				assert_eq!(
					StakeTracker::approval_stake(&validator_id).unwrap(),
					StakeTracker::active_stake_of(&validator_id) +
						StakeTracker::active_stake_of(&nominator_id)
				);
				StakeTracker::on_validator_remove(&validator_id);
				assert_eq!(
					StakeTracker::approval_stake(&validator_id).unwrap(),
					StakeTracker::active_stake_of(&nominator_id)
				);
				assert_eq!(VoterList::count(), 1);
				assert_eq!(TargetList::count(), 0);
			}
		});
	}

	#[test]
	#[should_panic(expected = "Validator removed from TargetList; qed")]
	fn defensive_when_not_in_target_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(TargetList::count(), 0);
			StakeTracker::on_validator_remove(&10);
		});
	}

	#[test]
	#[should_panic(expected = "on_validator_remove is called for a validator; qed")]
	fn defensive_nominator() {
		ExtBuilder::default().build_and_execute(|| {
			let id = 20;
			assert_eq!(TargetList::count(), 0);
			StakeTracker::on_nominator_add(&id);
			StakeTracker::on_validator_remove(&id);
		});
	}

	#[test]
	#[should_panic(expected = "Validator removed from VoterList; qed")]
	fn defensive_when_not_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			assert_ok!(TargetList::on_insert(10, 10));
			StakeTracker::on_validator_remove(&10);
		});
	}
}

mod on_nominator_remove {
	use super::*;

	#[test]
	#[should_panic(expected = "Nominator removed from VoterList; qed")]
	fn defensive_when_not_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			StakeTracker::on_nominator_remove(&20, Vec::new());
		});
	}

	#[test]
	fn works_with_and_without_nominations() {
		ExtBuilder::default().build_and_execute(|| {
			let nominator_id = 20;

			let nominations = Staking::nominations(&nominator_id).unwrap();

			StakeTracker::on_nominator_add(&20);
			StakeTracker::on_validator_add(&10);
			StakeTracker::on_validator_add(&11);

			let check_nominations = || {
				for id in &nominations {
					assert_eq!(
						TargetList::get_score(id).unwrap(),
						StakeTracker::active_stake_of(id)
							.saturating_add(StakeTracker::active_stake_of(&nominator_id))
					);
					assert_eq!(
						StakeTracker::approval_stake(id).unwrap(),
						StakeTracker::active_stake_of(id)
							.saturating_add(StakeTracker::active_stake_of(&nominator_id))
					);
				}
			};

			check_nominations();

			StakeTracker::on_nominator_remove(&20, nominations.clone());

			for id in &nominations {
				assert_eq!(TargetList::get_score(id).unwrap(), StakeTracker::active_stake_of(id));
				assert_eq!(
					StakeTracker::approval_stake(id).unwrap(),
					StakeTracker::active_stake_of(id)
				);
			}

			StakeTracker::on_nominator_add(&20);
			StakeTracker::on_nominator_remove(&20, Vec::new());

			check_nominations();
		});
	}

	#[test]
	fn works_for_nominator_and_validator() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			let validator_id = 10;
			let nominator_id = 20;

			StakeTracker::on_nominator_add(&nominator_id);
			StakeTracker::on_nominator_remove(&nominator_id, Vec::new());

			assert_eq!(VoterList::count(), 0);

			StakeTracker::on_validator_add(&validator_id);
			StakeTracker::on_nominator_remove(&validator_id, Vec::new());

			assert_eq!(VoterList::count(), 0);
		});
	}
}

mod on_unstake {
	use super::*;

	#[test]
	fn noop_when_no_approval_stake() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// any staker
			for id in stakers() {
				assert_storage_noop!(StakeTracker::on_unstake(&id));
			}
		});
	}

	#[test]
	fn removes_approval_stake() {
		ExtBuilder::default().build_and_execute(|| {
			let validator_id = 10;
			ApprovalStake::<Runtime>::set(&validator_id, Some(1));
			StakeTracker::on_unstake(&validator_id);
			assert_eq!(StakeTracker::approval_stake(&validator_id), None);
		});
	}

	#[test]
	#[should_panic(expected = "The staker has already been removed from VoterList; qed")]
	fn defensive_when_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			let _ = VoterList::on_insert(10, 100);
			StakeTracker::on_unstake(&10);
		});
	}

	#[test]
	#[should_panic(expected = "The validator has already been removed from TargetList; qed")]
	fn defensive_when_in_target_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(TargetList::count(), 0);
			for id in stakers() {
				let _ = TargetList::on_insert(id, 100);
				StakeTracker::on_unstake(&id);
			}
		});
	}
}
