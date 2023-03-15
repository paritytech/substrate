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

use super::{mock::*, pallet::*};
use crate as pallet_stake_tracker;
use frame_election_provider_support::SortedListProvider;
use frame_support::{assert_err, assert_ok, assert_storage_noop};
use sp_staking::{OnStakingUpdate, Stake, StakingInterface};

pub(crate) type VoterList = <Runtime as pallet_stake_tracker::Config>::VoterList;
pub(crate) type TargetList = <Runtime as pallet_stake_tracker::Config>::TargetList;

// It is the caller's problem to make sure each of events is emitted in the right context, therefore
// we test each event for all the stakers (validators + nominators).

mod on_stake_update {
	use super::*;

	#[test]
	#[should_panic(expected = "on_stake_update should always be called on a bonded account!")]
	fn defensive_when_not_bonded() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			// user without stake
			assert_storage_noop!(StakeTracker::on_stake_update(&30, None));
		});
	}

	#[test]
	fn works_for_validators_and_nominators() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			assert_eq!(TargetList::count(), 0);

			let score = 1000;
			let stake = 0;
			let validator_id = 10;
			let validator2_id = 11;
			let nominator_id = 20;

			// validator
			let _ = VoterList::on_insert(validator_id, score).unwrap();
			let _ = TargetList::on_insert(validator_id, stake).unwrap();

			assert_eq!(VoterList::get_score(&validator_id).unwrap(), score);
			assert_eq!(TargetList::get_score(&validator_id).unwrap(), stake);

			// Previous stake is less than current (default: 0)
			let _ = StakeTracker::on_stake_update(&validator_id, None);
			// VoterList logic does not care about previous stake so we test it only once.
			assert_eq!(
				VoterList::get_score(&validator_id).unwrap(),
				StakeTracker::to_vote(StakeTracker::active_stake_of(&validator_id))
			);
			assert_eq!(
				TargetList::get_score(&validator_id).unwrap(),
				StakeTracker::active_stake_of(&validator_id)
			);

			// Previous stake is more than current 10 vs 9, ApprovalStake decrements by 1.
			let _ = StakeTracker::on_stake_update(
				&validator_id,
				Some(Stake { stash: validator_id, active: 10, total: 11 }),
			);

			assert_eq!(
				TargetList::get_score(&validator_id).unwrap(),
				StakeTracker::active_stake_of(&validator_id) - 1
			);

			// Previous stake is less than current 8 vs 9, ApprovalStake increments	 by 1.
			let _ = StakeTracker::on_stake_update(
				&validator_id,
				Some(Stake { stash: validator_id, active: 8, total: 9 }),
			);

			assert_eq!(
				TargetList::get_score(&validator_id).unwrap(),
				StakeTracker::active_stake_of(&validator_id)
			);

			assert_eq!(VoterList::count(), 1);
			assert_eq!(TargetList::count(), 1);

			// nominator
			let _ = VoterList::on_insert(nominator_id, score).unwrap();
			let _ = TargetList::on_insert(validator2_id, stake);

			// Nominating two validators, one already has their safe-stake, the other has 0.
			let _ = StakeTracker::on_stake_update(&nominator_id, None);
			assert_eq!(
				VoterList::get_score(&nominator_id).unwrap(),
				StakeTracker::to_vote(StakeTracker::active_stake_of(&nominator_id))
			);
			assert_eq!(
				TargetList::get_score(&validator_id).unwrap(),
				StakeTracker::active_stake_of(&nominator_id) +
					StakeTracker::active_stake_of(&validator_id)
			);
			assert_eq!(
				ApprovalStake::<Runtime>::get(validator_id).unwrap(),
				TargetList::get_score(&validator_id).unwrap()
			);
			assert_eq!(
				TargetList::get_score(&validator2_id).unwrap(),
				StakeTracker::active_stake_of(&nominator_id)
			);
			assert_eq!(
				ApprovalStake::<Runtime>::get(validator2_id).unwrap(),
				TargetList::get_score(&validator2_id).unwrap()
			);
			assert_eq!(VoterList::count(), 2);
			assert_eq!(TargetList::count(), 2);
		});
	}

	#[test]
	#[should_panic(expected = "Unable to update a nominator, perhaps it does not exist?")]
	fn defensive_when_not_in_list_nominator() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			for id in Nominators::get() {
				StakeTracker::on_stake_update(&id, None);
			}
		});
	}

	#[test]
	#[should_panic(expected = "Each validator must exist in the TargetList.")]
	fn defensive_when_not_in_target_list_validator() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			for id in Validators::get() {
				StakeTracker::on_stake_update(&id, None);
			}
		});
	}

	#[test]
	#[should_panic(expected = "Unable to update a validator, perhaps it does not exist?")]
	fn defensive_when_not_in_voter_list_validator() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			for id in Validators::get() {
				assert_ok!(TargetList::on_insert(id, 100));
				StakeTracker::on_stake_update(&id, None);
			}
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

			let mut nominations = nominations();

			for id in Nominators::get() {
				StakeTracker::on_nominator_add(&id);
				assert_eq!(
					VoterList::get_score(&id).unwrap(),
					StakeTracker::to_vote(StakeTracker::active_stake_of(&id))
				);
			}

			for (nomination, score) in nominations.clone() {
				assert_eq!(ApprovalStake::<Runtime>::get(nomination).unwrap_or_default(), score);
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
					ApprovalStake::<Runtime>::get(nomination).unwrap_or_default(),
					approval_stake
				);
				assert_eq!(
					ApprovalStake::<Runtime>::get(nomination).unwrap_or_default(),
					TargetList::get_score(nomination).unwrap()
				);
			}

			assert_eq!(VoterList::count(), (Nominators::get().len() + nominations.len()) as u32);
			assert_eq!(TargetList::count(), nominations.len() as u32);
		});
	}

	#[test]
	#[should_panic(expected = "Unable to insert a nominator, perhaps it already exists?")]
	fn defensive_when_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			for id in Nominators::get() {
				let _ = VoterList::on_insert(id, 100);
				StakeTracker::on_nominator_add(&id);
			}
		});
	}
}

mod on_nominator_update {
	use super::*;
	use frame_support::traits::Len;

	#[test]
	fn noop_for_non_nominator_and_empty_nominations() {
		ExtBuilder::default().build_and_execute(|| {
			// validators
			for id in Validators::get() {
				assert_storage_noop!(StakeTracker::on_nominator_update(&id, Vec::new()));
			}

			// nominators with no nominations
			for id in Nominators::get().iter().filter(|id| Staking::nominations(&id).len() == 0) {
				assert_storage_noop!(StakeTracker::on_nominator_update(&id, Vec::new()));
			}
		});
	}
	#[test]
	// It is the caller's problem to make sure `on_nominator_update` is called in the right context.
	fn nomination_scenarios() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// no prev nominations and nominations are not in TargetList
			StakeTracker::on_nominator_update(&20, Vec::new());

			for nomination in Staking::nominations(&20).unwrap() {
				assert_err!(
					TargetList::get_score(&nomination),
					pallet_bags_list::ListError::NodeNotFound
				);
				assert_eq!(
					StakeTracker::approval_stake(&nomination).unwrap(),
					StakeTracker::active_stake_of(&20)
				);
			}

			assert_eq!(ApprovalStake::<Runtime>::count(), 2);
			let _ = ApprovalStake::<Runtime>::clear(100, None);

			// no prev nominations and nominations are in TargetList
			for nomination in Staking::nominations(&20).unwrap() {
				let _ = StakeTracker::on_validator_add(&nomination);
			}

			StakeTracker::on_nominator_update(&20, Vec::new());

			for nomination in Staking::nominations(&20).unwrap() {
				assert_eq!(
					TargetList::get_score(&nomination).unwrap(),
					StakeTracker::active_stake_of(&20)
						.saturating_add(StakeTracker::active_stake_of(&nomination))
				);
				assert_eq!(
					ApprovalStake::<Runtime>::get(&nomination).unwrap(),
					StakeTracker::active_stake_of(&20)
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
			StakeTracker::on_nominator_update(&20, vec![11, 12]);

			assert_eq!(
				TargetList::get_score(&12).unwrap(),
				StakeTracker::active_stake_of(&12)
					.saturating_sub(StakeTracker::active_stake_of(&20))
			);
			assert_eq!(
				StakeTracker::approval_stake(&12).unwrap(),
				StakeTracker::active_stake_of(&12)
					.saturating_sub(StakeTracker::active_stake_of(&20))
			);

			assert_eq!(
				TargetList::get_score(&10).unwrap(),
				StakeTracker::active_stake_of(&20)
					.saturating_add(StakeTracker::active_stake_of(&10))
			);
			assert_eq!(
				StakeTracker::approval_stake(&10).unwrap(),
				StakeTracker::active_stake_of(&20)
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

			// nominators + validators
			for id in stakers() {
				StakeTracker::on_validator_add(&id);
				assert_eq!(
					VoterList::get_score(&id).unwrap(),
					StakeTracker::to_vote(StakeTracker::active_stake_of(&id))
				);
				assert_eq!(
					TargetList::get_score(&id).unwrap(),
					ApprovalStake::<Runtime>::get(&id).unwrap()
				);
			}

			assert_eq!(VoterList::count(), stakers().len() as u32);
			assert_eq!(TargetList::count(), stakers().len() as u32);
		});
	}

	#[test]
	fn works_with_existing_approval_stake() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			assert_eq!(TargetList::count(), 0);

			let initial_approval_stake = 100;

			// nominators + validators
			for id in stakers() {
				ApprovalStake::<Runtime>::set(&id, Some(initial_approval_stake));
				StakeTracker::on_validator_add(&id);
				assert_eq!(
					VoterList::get_score(&id).unwrap(),
					StakeTracker::to_vote(StakeTracker::active_stake_of(&id))
				);
				assert_eq!(
					TargetList::get_score(&id).unwrap(),
					ApprovalStake::<Runtime>::get(&id).unwrap()
				);
				assert_eq!(
					ApprovalStake::<Runtime>::get(&id).unwrap(),
					StakeTracker::active_stake_of(&id) + initial_approval_stake,
				);
			}

			assert_eq!(VoterList::count(), stakers().len() as u32);
			assert_eq!(TargetList::count(), stakers().len() as u32);
		});
	}

	#[test]
	#[should_panic(
		expected = "Unable to insert a validator into VoterList, perhaps it already exists?"
	)]
	fn defensive_when_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			for id in Validators::get() {
				let _ = VoterList::on_insert(id, 100);
				StakeTracker::on_validator_add(&id);
			}
		});
	}

	#[test]
	#[should_panic(
		expected = "Unable to insert a validator into TargetList, perhaps it already exists?"
	)]
	fn defensive_when_in_target_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(TargetList::count(), 0);
			for id in Validators::get() {
				let _ = TargetList::on_insert(id, 100);
				StakeTracker::on_validator_add(&id);
			}
		});
	}
}

mod on_validator_update {
	use super::*;
	#[test]
	fn noop_when_in_the_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// usual user, validator, nominator
			for id in stakers() {
				let _ = VoterList::on_insert(id, 1000);
				assert_storage_noop!(StakeTracker::on_validator_update(&id));
			}
		});
	}

	#[test]
	fn noop() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// validators + nominators
			for id in stakers() {
				assert_storage_noop!(StakeTracker::on_validator_update(&id));
			}
		});
	}
}

mod on_validator_remove {
	use super::*;

	#[test]
	fn works_for_everyone() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			assert_eq!(TargetList::count(), 0);

			// nominators + validators
			for id in stakers() {
				StakeTracker::on_validator_add(&id);
				assert_eq!(VoterList::count(), 1);
				assert_eq!(TargetList::count(), 1);
				assert_eq!(
					ApprovalStake::<Runtime>::get(&id).unwrap(),
					TargetList::get_score(&id).unwrap()
				);
				assert_eq!(
					ApprovalStake::<Runtime>::get(&id).unwrap(),
					StakeTracker::active_stake_of(&id)
				);
				StakeTracker::on_validator_remove(&id);
				assert_eq!(ApprovalStake::<Runtime>::get(&id).unwrap(), 0);
				assert_eq!(VoterList::count(), 0);
				assert_eq!(TargetList::count(), 0);
			}
		});
	}

	#[test]
	#[should_panic(
		expected = "Unable to remove a validator from VoterList, perhaps it does not exist?"
	)]
	fn defensive_when_not_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			for id in Validators::get() {
				assert_ok!(TargetList::on_insert(id, 100));
				StakeTracker::on_validator_remove(&id);
			}
		});
	}

	#[test]
	#[should_panic(
		expected = "Unable to remove an entry from TargetList, perhaps it does not exist?"
	)]
	fn defensive_when_not_in_target_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(TargetList::count(), 0);
			for id in Validators::get() {
				StakeTracker::on_validator_remove(&id);
			}
		});
	}
}

mod on_nominator_remove {
	use super::*;

	fn with_nominations() {
		ExtBuilder::default().build_and_execute(|| {
			// no entries in TargetList or ApprovalStake
			// validators, nominators
			for id in stakers() {
				assert_storage_noop!(StakeTracker::on_nominator_remove(&id, vec![10, 11]));
			}

			// with entries in TargetList and ApprovalStake

			let nominations = vec![10, 11];

			StakeTracker::on_validator_add(&10);
			StakeTracker::on_validator_add(&11);
			StakeTracker::on_nominator_remove(&20, nominations.clone());

			for id in nominations {
				assert_eq!(
					TargetList::get_score(&id).unwrap(),
					StakeTracker::active_stake_of(&id)
						.saturating_sub(StakeTracker::active_stake_of(&20))
				);
				assert_eq!(
					StakeTracker::approval_stake(&id).unwrap(),
					StakeTracker::active_stake_of(&id)
						.saturating_sub(StakeTracker::active_stake_of(&20))
				);
			}
		});
	}

	#[test]
	#[should_panic(expected = "Unable to remove a nominator, perhaps it does not exist?")]
	fn defensive_when_not_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			for id in Nominators::get() {
				StakeTracker::on_nominator_remove(&id, vec![]);
			}
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
			assert_eq!(VoterList::count(), 0);

			// any staker
			for id in stakers() {
				ApprovalStake::<Runtime>::set(&id, Some(1));
				StakeTracker::on_unstake(&id);
				assert_eq!(ApprovalStake::<Runtime>::get(&id), None);
			}
		});
	}

	#[test]
	#[should_panic(expected = "The staker should have already been removed!")]
	fn defensive_when_in_voter_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			for id in stakers() {
				let _ = VoterList::on_insert(id, 100);
				StakeTracker::on_unstake(&id);
			}
		});
	}

	#[test]
	#[should_panic(expected = "The validator should have already been removed!")]
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
