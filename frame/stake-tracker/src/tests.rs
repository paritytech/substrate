use super::{mock::*, pallet::*};
use crate as pallet_stake_tracker;
use frame_election_provider_support::{ReadOnlySortedListProvider, SortedListProvider};
use frame_support::{assert_ok, assert_storage_noop};
use sp_staking::{OnStakingUpdate, Stake, StakingInterface};

type VoterList = <Runtime as pallet_stake_tracker::Config>::VoterList;
type TargetList = <Runtime as pallet_stake_tracker::Config>::TargetList;
type Staking = <Runtime as pallet_stake_tracker::Config>::Staking;

mod on_stake_update {
	use super::*;
	#[test]
	fn empty_lists() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);
			assert_eq!(TargetList::count(), 0);
			let validator_id = &10;
			// usual user
			assert_storage_noop!(StakeTracker::on_stake_update(&1, None));
			// validator
			StakeTracker::on_stake_update(validator_id, None);
			assert_eq!(
				ApprovalStake::<Runtime>::get(validator_id).unwrap(),
				StakeTracker::slashable_balance_of(validator_id)
			);
			assert_eq!(ApprovalStake::<Runtime>::count(), 1);

			// nominator
			StakeTracker::on_stake_update(&20, None);
			assert_eq!(
				ApprovalStake::<Runtime>::get(validator_id).unwrap(),
				StakeTracker::slashable_balance_of(validator_id) +
					StakeTracker::slashable_balance_of(&20)
			);
			assert_eq!(
				StakeTracker::approval_stake(&11).unwrap(),
				StakeTracker::slashable_balance_of(&20)
			);
			assert_eq!(ApprovalStake::<Runtime>::count(), 2);
			assert_eq!(VoterList::count(), 0);
			assert_eq!(TargetList::count(), 0);
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
				StakeTracker::to_vote(StakeTracker::slashable_balance_of(&validator_id))
			);
			assert_eq!(
				TargetList::get_score(&validator_id).unwrap(),
				StakeTracker::slashable_balance_of(&validator_id)
			);

			// Previous stake is more than current 10 vs 9, ApprovalStake decrements by 1.
			let _ = StakeTracker::on_stake_update(
				&validator_id,
				Some(Stake { stash: validator_id, active: 10, total: 11 }),
			);

			assert_eq!(
				TargetList::get_score(&validator_id).unwrap(),
				StakeTracker::slashable_balance_of(&validator_id) - 1
			);

			// Previous stake is less than current 8 vs 9, ApprovalStake increments	 by 1.
			let _ = StakeTracker::on_stake_update(
				&validator_id,
				Some(Stake { stash: validator_id, active: 8, total: 9 }),
			);

			assert_eq!(
				TargetList::get_score(&validator_id).unwrap(),
				StakeTracker::slashable_balance_of(&validator_id)
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
				StakeTracker::to_vote(StakeTracker::slashable_balance_of(&nominator_id))
			);
			assert_eq!(
				TargetList::get_score(&validator_id).unwrap(),
				StakeTracker::slashable_balance_of(&nominator_id) +
					StakeTracker::slashable_balance_of(&validator_id)
			);
			assert_eq!(
				ApprovalStake::<Runtime>::get(validator_id).unwrap(),
				TargetList::get_score(&validator_id).unwrap()
			);
			assert_eq!(
				TargetList::get_score(&validator2_id).unwrap(),
				StakeTracker::slashable_balance_of(&nominator_id)
			);
			assert_eq!(
				ApprovalStake::<Runtime>::get(validator2_id).unwrap(),
				TargetList::get_score(&validator2_id).unwrap()
			);
			assert_eq!(VoterList::count(), 2);
			assert_eq!(TargetList::count(), 2);
		});
	}
}

mod on_nominator_update {
	use super::*;
	use frame_support::assert_err;
	#[test]
	fn noop_for_non_nominator() {
		ExtBuilder::default().build_and_execute(|| {
			// usual user, validator, not bonded user
			for id in [1, 10, 30] {
				assert_storage_noop!(StakeTracker::on_nominator_update(&id, Vec::new()));
			}
		});
	}

	#[test]
	fn nominator_in_the_list_empty_nominations() {
		ExtBuilder::default().build_and_execute(|| {
			let _ = VoterList::on_insert(22, 1);
			assert_storage_noop!(StakeTracker::on_nominator_update(&22, Vec::new()));
			StakeTracker::on_nominator_update(&23, Vec::new());
			assert_eq!(
				VoterList::get_score(&23).unwrap(),
				StakeTracker::to_vote(Staking::stake(&23).map(|s| s.active).unwrap())
			)
		});
	}

	#[test]
	// It is the caller's problem to make sure `on_nominator_update` is called in the right context.
	fn nomination_scenarios() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(VoterList::count(), 0);

			// no prev nominations and nominations are not in TargetList
			StakeTracker::on_nominator_update(&20, Vec::new());
			assert_eq!(
				VoterList::get_score(&20).unwrap(),
				StakeTracker::to_vote(Staking::stake(&20).map(|s| s.active).unwrap())
			);

			for nomination in Staking::nominations(&20).unwrap() {
				assert_err!(
					TargetList::get_score(&nomination),
					pallet_bags_list::ListError::NodeNotFound
				);
			}

			// no prev nominations and nominations are in TargetList
			for nomination in Staking::nominations(&20).unwrap() {
				let _ = StakeTracker::on_validator_add(&nomination);
			}

			StakeTracker::on_nominator_update(&20, Vec::new());
			assert_eq!(
				VoterList::get_score(&20).unwrap(),
				StakeTracker::to_vote(Staking::stake(&20).unwrap().active)
			);

			for nomination in Staking::nominations(&20).unwrap() {
				assert_eq!(
					TargetList::get_score(&nomination).unwrap(),
					StakeTracker::slashable_balance_of(&20)
						.saturating_add(StakeTracker::slashable_balance_of(&nomination))
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
					StakeTracker::to_vote(Staking::stake(&id).map(|s| s.active).unwrap())
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
