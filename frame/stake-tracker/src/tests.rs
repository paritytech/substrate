// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use crate::mock::*;

use frame_election_provider_support::SortedListProvider;
use sp_staking::{Stake, StakingInterface};

#[test]
fn setup_works() {
	ExtBuilder::default().build_and_execute(|| {
		assert!(TestNominators::get().is_empty());
		assert_eq!(VoterBagsList::count(), 0);

		assert!(TestValidators::get().is_empty());
		assert_eq!(TargetBagsList::count(), 0);
	});

	ExtBuilder::default().populate_lists().build_and_execute(|| {
		assert!(!TestNominators::get().is_empty());
		assert_eq!(VoterBagsList::count(), 4); // 2x nominators + 2x validators

		assert!(!TestValidators::get().is_empty());
		assert_eq!(TargetBagsList::count(), 2);
	});
}

#[test]
fn staking_interface_works() {
	ExtBuilder::default().build_and_execute(|| {
		add_nominator(1, 100);
		let n = TestNominators::get();
		assert_eq!(n.get(&1).unwrap().0, Stake { active: 100u64, total: 100u64 });

		add_validator(2, 200);
		let v = TestValidators::get();
		assert_eq!(v.get(&2).copied().unwrap(), Stake { active: 200u64, total: 200u64 });
	})
}

#[test]
fn on_add_stakers_works() {
	ExtBuilder::default().build_and_execute(|| {
		add_nominator(1, 100);

		assert_eq!(TargetBagsList::count(), 0);
		assert_eq!(VoterBagsList::count(), 1);
		assert_eq!(VoterBagsList::get_score(&1).unwrap(), 100);

		add_validator(10, 200);
		assert_eq!(VoterBagsList::count(), 2); // 1x nominator + 1x validator
		assert_eq!(TargetBagsList::count(), 1);
		assert_eq!(TargetBagsList::get_score(&10).unwrap(), 200);
	})
}

#[test]
fn on_update_stake_works() {
	ExtBuilder::default().build_and_execute(|| {
		add_nominator(1, 100);
		assert_eq!(VoterBagsList::get_score(&1).unwrap(), 100);
		update_stake(1, 200);
		assert_eq!(VoterBagsList::get_score(&1).unwrap(), 200);

		add_validator(10, 100);
		assert_eq!(TargetBagsList::get_score(&10).unwrap(), 100);
		update_stake(10, 200);
		assert_eq!(TargetBagsList::get_score(&10).unwrap(), 200);
	})
}

#[test]
fn on_remove_stakers_works() {
	ExtBuilder::default().build_and_execute(|| {
		add_nominator(1, 100);
		assert!(VoterBagsList::contains(&1));
		remove_staker(1);
		assert!(!VoterBagsList::contains(&1));

		add_validator(10, 100);
		assert!(TargetBagsList::contains(&10));
		remove_staker(10);
		assert!(!TargetBagsList::contains(&10));
	})
}

#[test]
fn on_remove_stakers_with_nominations_works() {
	ExtBuilder::default().populate_lists().build_and_execute(|| {
		assert_eq!(get_scores::<TargetBagsList>(), vec![(10, 300), (11, 200)]);

		assert!(VoterBagsList::contains(&1));
		assert_eq!(VoterBagsList::get_score(&1), Ok(100));
		assert_eq!(TargetBagsList::get_score(&10), Ok(300));

		// remove nominator deletes node from voter list and updates the stake of its nominations.
		remove_staker(1);
		assert!(!VoterBagsList::contains(&1));
		assert_eq!(TargetBagsList::get_score(&10), Ok(200));
	})
}

#[test]
fn on_nominator_update_works() {
	ExtBuilder::default().populate_lists().build_and_execute(|| {
		assert_eq!(get_scores::<VoterBagsList>(), vec![(10, 100), (11, 100), (1, 100), (2, 100)]);
		assert_eq!(get_scores::<TargetBagsList>(), vec![(10, 300), (11, 200)]);

		add_validator(20, 50);
		// removes nomination from 10 and adds nomination to new validator, 20.
		update_nominations_of(2, vec![11, 20]);

		// new voter (validator) 2 with 100 stake. note that the voter score is not updated
		// automatically.
		assert_eq!(
			get_scores::<VoterBagsList>(),
			vec![(10, 100), (11, 100), (1, 100), (2, 100), (20, 50)]
		);

		// target list has been updated:
		// -100 score for 10
		// +100 score for 11
		// +100 score for 20
		assert_eq!(get_scores::<TargetBagsList>(), vec![(10, 200), (11, 200), (20, 150)]);
	})
}

#[test]
fn on_slash_works() {
	ExtBuilder::default().populate_lists().build_and_execute(|| {
		assert_eq!(get_scores::<VoterBagsList>(), vec![(10, 100), (11, 100), (1, 100), (2, 100)]);
		assert_eq!(get_scores::<TargetBagsList>(), vec![(10, 300), (11, 200)]);

		// slash nominator 2.
		slash(2, 10, Default::default());

		// voters list is not updated automatically upon slash.
		assert_eq!(get_scores::<VoterBagsList>(), vec![(10, 100), (11, 100), (1, 100), (2, 100)]);

		// targets list nominated by the slashed nominator are affected.
		assert_eq!(<StakingMock as StakingInterface>::nominations(&2).unwrap(), vec![10, 11]);
		assert_eq!(get_scores::<TargetBagsList>(), vec![(10, 290), (11, 190)]);
	})
}
