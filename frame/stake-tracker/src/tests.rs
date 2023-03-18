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
use frame_support::{assert_storage_noop, traits::fungible::Mutate};
use sp_staking::OnStakingUpdate;

type VoterList = <Runtime as pallet_stake_tracker::Config>::VoterList;

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
	fn works() {
		ExtBuilder::default().build_and_execute(|| {
			let balance_before: Balance = 1000;
			let balance_after: Balance = 10;
			let validator_id = 10;
			let nominator_id = 20;
			assert_eq!(VoterList::count(), 0);

			// validator
			Balances::set_balance(&validator_id, balance_before);
			StakeTracker::on_validator_add(&validator_id);
			assert_eq!(
				VoterList::get_score(&validator_id).unwrap(),
				StakeTracker::to_vote(StakeTracker::active_stake_of(&validator_id))
			);

			Balances::set_balance(&validator_id, balance_after);
			StakeTracker::on_stake_update(&validator_id, None);
			assert_eq!(
				VoterList::get_score(&validator_id).unwrap(),
				StakeTracker::to_vote(StakeTracker::active_stake_of(&validator_id))
			);

			// nominator
			Balances::set_balance(&nominator_id, balance_before);
			StakeTracker::on_nominator_add(&nominator_id);
			assert_eq!(
				VoterList::get_score(&nominator_id).unwrap(),
				StakeTracker::to_vote(StakeTracker::active_stake_of(&nominator_id))
			);

			Balances::set_balance(&nominator_id, balance_after);
			StakeTracker::on_stake_update(&nominator_id, None);
			assert_eq!(
				VoterList::get_score(&nominator_id).unwrap(),
				StakeTracker::to_vote(StakeTracker::active_stake_of(&nominator_id))
			);

			assert_eq!(VoterList::count(), 2);
		});
	}

	#[test]
	#[should_panic(expected = "Nominator's position in VoterList updated; qed")]
	fn defensive_when_not_in_list_nominator() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			for id in Nominators::get() {
				StakeTracker::on_stake_update(&id, None);
			}
		});
	}

	#[test]
	#[should_panic(expected = "Validator's position in VoterList updated; qed")]
	fn defensive_when_not_in_list_validator() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			for id in Validators::get() {
				StakeTracker::on_stake_update(&id, None);
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

			// nominators
			for id in Nominators::get() {
				StakeTracker::on_nominator_add(&id);
				assert_eq!(
					VoterList::get_score(&id).unwrap(),
					StakeTracker::to_vote(StakeTracker::active_stake_of(&id))
				);
			}

			assert_eq!(VoterList::count(), Nominators::get().len() as u32);
		});
	}

	#[test]
	#[should_panic(expected = "Nominator inserted into VoterList; qed")]
	fn defensive_when_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			for id in Nominators::get() {
				StakeTracker::on_nominator_add(&id);
				StakeTracker::on_nominator_add(&id);
			}
		});
	}
}

mod on_nominator_update {
	use super::*;

	#[test]
	#[should_panic(expected = "Active nominator is in the VoterList; qed")]
	fn defensive_not_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			StakeTracker::on_nominator_update(&20, Vec::new())
		});
	}

	#[test]
	fn noop() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			let id = 20;

			StakeTracker::on_nominator_add(&id);
			assert_storage_noop!(StakeTracker::on_nominator_update(&id, Vec::new()));
			assert_eq!(VoterList::count(), 1);
		});
	}
}

mod on_validator_add {
	use super::*;

	#[test]
	fn works() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// validators
			for id in Validators::get() {
				StakeTracker::on_validator_add(&id);
				assert_eq!(
					VoterList::get_score(&id).unwrap(),
					StakeTracker::to_vote(StakeTracker::active_stake_of(&id))
				);
			}

			assert_eq!(VoterList::count(), Validators::get().len() as u32);
		});
	}

	#[test]
	#[should_panic(expected = "Validator inserted into VoterList; qed")]
	fn defensive_when_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			let id = 10;
			StakeTracker::on_validator_add(&id);
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
	fn defensive_not_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			StakeTracker::on_validator_update(&10)
		});
	}
}

mod on_validator_remove {
	use super::*;

	#[test]
	fn works_for_validator_and_nominator() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			let validator_id = 10;
			let nominator_id = 20;

			StakeTracker::on_validator_add(&validator_id);
			StakeTracker::on_validator_remove(&validator_id);

			assert_eq!(VoterList::count(), 0);

			StakeTracker::on_nominator_add(&nominator_id);
			StakeTracker::on_validator_remove(&nominator_id);

			assert_eq!(VoterList::count(), 0);
		});
	}

	#[test]
	#[should_panic(expected = "Validator removed from VoterList; qed")]
	fn defensive_when_not_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			StakeTracker::on_validator_remove(&10);
		});
	}
}

mod on_nominator_remove {
	use super::*;

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

	#[test]
	#[should_panic(expected = "Nominator removed from VoterList; qed")]
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

	#[test]
	#[should_panic(expected = "The staker has already been removed; qed")]
	fn defensive_when_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			for id in stakers() {
				let _ = VoterList::on_insert(id, 100);
				StakeTracker::on_unstake(&id);
			}
		});
	}
}
