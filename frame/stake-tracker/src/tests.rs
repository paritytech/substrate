use super::{mock::*, pallet::*};
use crate as pallet_stake_tracker;
use frame_election_provider_support::{ReadOnlySortedListProvider, SortedListProvider};
use frame_support::{assert_ok, assert_storage_noop};
use sp_staking::{OnStakingUpdate, StakingInterface};

type VoterList = <Runtime as pallet_stake_tracker::Config>::VoterList;
type Staking = <Runtime as pallet_stake_tracker::Config>::Staking;

mod on_stake_update {
	use super::*;
	#[test]
	fn noop_when_not_in_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			// usual user
			assert_storage_noop!(StakeTracker::on_stake_update(&1, None));
			// validator
			assert_storage_noop!(StakeTracker::on_stake_update(&10, None));
			// nominator
			assert_storage_noop!(StakeTracker::on_stake_update(&20, None));
		});
	}

	#[test]
	#[should_panic]
	fn panics_when_not_bonded() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			// user without stake
			assert_storage_noop!(StakeTracker::on_stake_update(&30, None));
		});
	}

	#[test]
	fn noop_when_not_validator_or_nominator() {
		ExtBuilder::default().build_and_execute(|| {
			VoterList::on_insert(1, 10000).unwrap();
			// usual user
			assert_storage_noop!(StakeTracker::on_stake_update(&1, None));
		});
	}

	#[test]
	fn works_for_validators_and_nominators() {
		ExtBuilder::default().build_and_execute(|| {
			let score = 1000;
			assert_eq!(VoterList::count(), 0);
			// validator, nominator
			for (idx, id) in [10, 20].iter().enumerate() {
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

mod on_nominator_update {
	use super::*;
	#[test]
	fn noop_when_in_the_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// usual user, validator, nominator
			for id in [1, 10, 20] {
				let _ = VoterList::on_insert(id, 1000);
				assert_storage_noop!(StakeTracker::on_nominator_update(&id, Vec::new()));
			}
		});
	}

	#[test]
	#[should_panic]
	fn panics_when_not_bonded() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			// user without stake
			assert_storage_noop!(StakeTracker::on_nominator_update(&30, Vec::new()));
		});
	}

	#[test]
	// It is the caller's problem to make sure `on_nominator_update` is called in the right context.
	fn works_for_everyone() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// usual user, validator, nominator
			for id in [1, 10, 20] {
				StakeTracker::on_nominator_update(&id, Vec::new());
				assert_eq!(
					VoterList::get_score(&id).unwrap(),
					Pallet::<Runtime>::to_vote(Staking::stake(&id).map(|s| s.active).unwrap())
				);
			}
		});
	}
}

mod on_validator_add {
	use super::*;
	#[test]
	fn noop_when_in_the_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// usual user, validator, nominator
			for id in [1, 10, 20] {
				let _ = VoterList::on_insert(id, 1000);
				assert_storage_noop!(StakeTracker::on_validator_add(&id));
			}
		});
	}

	#[test]
	#[should_panic]
	fn panics_when_not_bonded() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			// user without stake
			assert_storage_noop!(StakeTracker::on_validator_add(&30));
		});
	}

	#[test]
	// It is the caller's problem to make sure `on_validator_add` is called in the right context.
	fn works_for_everyone() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// usual user, validator, nominator
			for id in [1, 10, 20] {
				StakeTracker::on_validator_add(&id);
				assert_eq!(
					VoterList::get_score(&id).unwrap(),
					Pallet::<Runtime>::to_vote(Staking::stake(&id).map(|s| s.active).unwrap())
				);
			}
		});
	}
}

mod on_validator_remove {
	use super::*;
	#[test]
	fn noop_when_not_in_the_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// usual user, validator, nominator, not bonded
			for id in [1, 10, 20, 30] {
				assert_storage_noop!(StakeTracker::on_validator_remove(&id));
			}
		});
	}

	#[test]
	// It is the caller's problem to make sure `on_validator_remove` is called in the right context.
	fn works_for_everyone_also_unbonded() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// usual user, validator, nominator
			for id in [1, 10, 20, 30] {
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
	fn noop_when_not_in_the_list() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// usual user, validator, nominator, not bonded
			for id in [1, 10, 20, 30] {
				assert_storage_noop!(StakeTracker::on_nominator_remove(&id, Vec::new()));
			}
		});
	}

	#[test]
	// It is the caller's problem to make sure `on_nominator_remove` is called in the right context.
	fn works_for_everyone_also_unbonded() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// usual user, validator, nominator
			for id in [1, 10, 20, 30] {
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
	fn noop() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// usual user, validator, nominator, not bonded
			for id in [1, 10, 20, 30] {
				assert_storage_noop!(StakeTracker::on_unstake(&id));
			}

			// usual user, validator, nominator, not bonded
			for id in [1, 10, 20, 30] {
				assert_ok!(VoterList::on_insert(id, 100));
				assert_storage_noop!(StakeTracker::on_unstake(&id));
			}
		});
	}
}
