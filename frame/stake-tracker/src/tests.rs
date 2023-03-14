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
use frame_support::assert_storage_noop;
use sp_staking::{OnStakingUpdate, StakingInterface};

type VoterList = <Runtime as pallet_stake_tracker::Config>::VoterList;
type Staking = <Runtime as pallet_stake_tracker::Config>::Staking;

// It is the caller's problem to make sure each of events is emitted in the right context, therefore
// we test each event for all the stakers (validators + nominators).

mod on_stake_update {
	use super::*;

	#[test]
	fn does_nothing_when_not_bonded() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			// user without stake
			assert_storage_noop!(StakeTracker::on_stake_update(&30, None));
		});
	}

	#[test]
	fn works_for_validators_and_nominators() {
		ExtBuilder::default().build_and_execute(|| {
			let score = 1000;
			assert_eq!(VoterList::count(), 0);
			// validator, nominator
			for (idx, id) in stakers().iter().enumerate() {
				let _ = VoterList::on_insert(*id, score).unwrap();
				assert_eq!(VoterList::count() as usize, idx + 1);
				assert_eq!(VoterList::get_score(id).unwrap(), score);
				let _ = StakeTracker::on_stake_update(id, None);
				assert_eq!(
					VoterList::get_score(id).unwrap(),
					Pallet::<Runtime>::to_vote(Staking::stake(id).map(|s| s.active).unwrap())
				);
			}
		});
	}
}

mod on_nominator_add {
	use super::*;

	#[test]
	fn works() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// nominators + validators
			for id in stakers() {
				StakeTracker::on_nominator_add(&id);
				assert_eq!(
					VoterList::get_score(&id).unwrap(),
					StakeTracker::to_vote(StakeTracker::active_stake_of(&id))
				);
			}

			assert_eq!(VoterList::count(), stakers().len() as u32);
		});
	}
}

mod on_nominator_update {
	use super::*;

	#[test]
	fn always_noop() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// not in list
			// validator, nominator
			for id in stakers() {
				assert_storage_noop!(StakeTracker::on_nominator_update(&id, Vec::new()));
			}

			// in list
			// validator, nominator
			for id in stakers() {
				let _ = VoterList::on_insert(id, 1000);
				assert_storage_noop!(StakeTracker::on_nominator_update(&id, Vec::new()));
			}
		});
	}
}

mod on_validator_add {
	use super::*;

	#[test]
	fn works() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// nominators + validators
			for id in stakers() {
				StakeTracker::on_validator_add(&id);
				assert_eq!(
					VoterList::get_score(&id).unwrap(),
					StakeTracker::to_vote(StakeTracker::active_stake_of(&id))
				);
			}

			assert_eq!(VoterList::count(), stakers().len() as u32);
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
	// It is the caller's problem to make sure `on_validator_remove` is called in the right context.
	fn works_for_everyone() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// nominators + validators
			for id in stakers() {
				let _ = VoterList::on_insert(id, 100);
				assert_eq!(VoterList::count(), 1);
				StakeTracker::on_validator_remove(&id);
				assert_eq!(VoterList::count(), 0);
			}
		});
	}
}

mod on_nominator_remove {
	use super::*;

	#[test]
	// It is the caller's problem to make sure `on_nominator_remove` is called in the right context.
	fn works_for_everyone() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// nominators + validators
			for id in stakers() {
				let _ = VoterList::on_insert(id, 100);
				assert_eq!(VoterList::count(), 1);
				StakeTracker::on_nominator_remove(&id, Vec::new());
				assert_eq!(VoterList::count(), 0);
			}
		});
	}
}

mod on_unstake {
	use super::*;

	#[test]
	// By the time this is called - staker has to already be removed from the list. Otherwise we hit
	// the defensive path.
	fn noop_when_not_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// any staker
			for id in stakers() {
				assert_storage_noop!(StakeTracker::on_unstake(&id));
			}
		});
	}
}
