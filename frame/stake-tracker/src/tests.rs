use super::{mock::*, pallet::*};
use crate as pallet_stake_tracker;
use frame_election_provider_support::{ReadOnlySortedListProvider, SortedListProvider};
use frame_support::assert_storage_noop;
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
