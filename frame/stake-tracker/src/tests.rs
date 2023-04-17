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
use frame_election_provider_support::{SortedListProvider, VoteWeight};
use frame_support::assert_storage_noop;
use sp_staking::OnStakingUpdate;

type VoterList = VoterBagsList;

fn backend() -> Vec<AccountId> {
	VoterList::iter().collect::<Vec<_>>()
}

#[test]
fn initial_state_works() {
	ExtBuilder::default().build_and_execute(|| {
		assert_eq!(TestValidators::get().len(), 3);
		assert_eq!(TestNominators::get().len(), 3);
		assert_eq!(VoterList::count(), 6);

		for (v, s) in TestValidators::get().iter() {
			assert_eq!(VoterList::get_score(v).unwrap(), *s as VoteWeight);
		}

		for (n, s) in TestNominators::get().iter() {
			assert_eq!(VoterList::get_score(n).unwrap(), *s as VoteWeight);
		}

		// initial validators
		assert_eq!(TestValidators::get().keys().cloned().collect::<Vec<_>>(), vec![10, 20, 30]);
		// initial nominators

		assert_eq!(TestNominators::get().keys().cloned().collect::<Vec<_>>(), vec![5u64, 15, 25]);

		// initial voters.
		assert_eq!(backend(), vec![30, 25, 20, 15, 10, 5]);
	})
}

mod on_stake_update {
	use super::*;

	#[test]
	#[should_panic(
		expected = "Defensive failure has been triggered!: \"received update for a staker who is not a staker\""
	)]
	fn not_bonded() {
		ExtBuilder::default().build_and_execute(|| StakeTracker::on_stake_update(&42, None));
	}

	#[test]
	fn validator() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(backend(), vec![30, 25, 20, 15, 10, 5]);

			// when
			set_validator_stake(10, 22);

			// then 10 gets promoted.
			assert_eq!(backend(), vec![30, 25, 10, 20, 15, 5]);
		})
	}

	#[test]
	fn nominator() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(backend(), vec![30, 25, 20, 15, 10, 5]);

			// when
			set_nominator_stake(5, 12);

			// then 10 gets promoted.
			assert_eq!(backend(), vec![30, 25, 20, 15, 5, 10]);
		})
	}
}

mod on_nominator_add {
	use super::*;

	#[test]
	fn works() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(backend(), vec![30, 25, 20, 15, 10, 5]);

			// when
			add_nominator(35, 35);

			// then 35 is inserted.
			assert_eq!(backend(), vec![35, 30, 25, 20, 15, 10, 5]);

			// when
			add_nominator(6, 6);

			// then 6 is inserted.
			assert_eq!(backend(), vec![35, 30, 25, 20, 15, 10, 5, 6]);
		});
	}

	#[test]
	#[should_panic(expected = "existent nominator would not be added again; qed")]
	fn defensive_when_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			let n = TestNominators::get();
			let existing = n.iter().next().unwrap().0;
			StakeTracker::on_nominator_add(&existing);
		});
	}
}

mod on_nominator_update {
	use super::*;

	#[test]
	#[should_panic(expected = "non-existent nominator would not be updated; qed")]
	fn defensive_not_in_list() {
		ExtBuilder::default()
			.build_and_execute(|| StakeTracker::on_nominator_update(&42, Vec::new()));
	}

	#[test]
	fn noop_if_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(backend(), vec![30, 25, 20, 15, 10, 5]);

			// when, then
			assert_storage_noop!(StakeTracker::on_nominator_update(&5, Vec::new()));
		});
	}
}

mod on_validator_add {
	use super::*;

	#[test]
	fn works() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(backend(), vec![30, 25, 20, 15, 10, 5]);

			// when
			add_validator(11, 11);

			// then
			assert_eq!(backend(), vec![30, 25, 20, 15, 11, 10, 5]);

			// when
			add_validator(40, 40);

			// then
			assert_eq!(backend(), vec![40, 30, 25, 20, 15, 11, 10, 5]);
		});
	}

	#[test]
	#[should_panic(expected = "existent validator would not be added again; qed")]
	fn defensive_when_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			let v = TestValidators::get();
			let existing = v.iter().next().unwrap().0;
			StakeTracker::on_validator_add(&existing);
		});
	}
}

mod on_validator_update {
	use super::*;

	#[test]
	fn noop_if_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(backend(), vec![30, 25, 20, 15, 10, 5]);

			// when, then
			assert_storage_noop!(StakeTracker::on_validator_update(&10));
		});
	}

	#[test]
	#[should_panic(expected = "non-existent validator would not be updated; qed")]
	fn defensive_when_not_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_storage_noop!(StakeTracker::on_validator_update(&42));
		});
	}
}

mod on_validator_remove {
	use super::*;

	#[test]
	fn works() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(backend(), vec![30, 25, 20, 15, 10, 5]);

			// when
			StakeTracker::on_validator_remove(&10);

			// then
			assert_eq!(backend(), vec![30, 25, 20, 15, 5]);

			// when
			StakeTracker::on_validator_remove(&30);

			// then
			assert_eq!(backend(), vec![25, 20, 15, 5]);
		});
	}

	#[test]
	#[should_panic(expected = "non-existent validator would be removed; qed")]
	fn defensive_when_not_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			StakeTracker::on_validator_remove(&42);
		});
	}
}

mod on_nominator_remove {
	use super::*;

	#[test]
	fn works() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(backend(), vec![30, 25, 20, 15, 10, 5]);

			// when
			StakeTracker::on_nominator_remove(&5, Default::default());

			// then
			assert_eq!(backend(), vec![30, 25, 20, 15, 10]);

			// when
			StakeTracker::on_nominator_remove(&25, Default::default());

			// then
			assert_eq!(backend(), vec![30, 20, 15, 10]);
		});
	}

	#[test]
	#[should_panic(expected = "non-existent nominator would bot be removed; qed")]
	fn defensive_when_not_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			StakeTracker::on_nominator_remove(&42, vec![]);
		});
	}
}

mod on_unstake {
	use super::*;

	#[test]
	fn noop_when_not_in_list_and_invalid() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(backend(), vec![30, 25, 20, 15, 10, 5]);

			// when a validator leaves.
			StakeTracker::on_validator_remove(&30);

			// then
			assert_eq!(backend(), vec![25, 20, 15, 10, 5]);
			assert_storage_noop!(StakeTracker::on_unstake(&30));

			// when a nominator leaves.
			StakeTracker::on_validator_remove(&25);

			// then
			assert_eq!(backend(), vec![20, 15, 10, 5]);
			assert_storage_noop!(StakeTracker::on_unstake(&25));

			// if a non-voter is unstaked
			assert_storage_noop!(StakeTracker::on_unstake(&42));
		});
	}

	#[test]
	#[should_panic(expected = "existent voter cannot be unstaked; qed")]
	fn defensive_when_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			StakeTracker::on_unstake(&10);
		});
	}
}
