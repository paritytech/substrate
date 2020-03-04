use crate::*;
use crate::mock::*;
use frame_support::storage::migration::*;
use sp_core::hashing::blake2_256;
use super::test_upgrade_from_master_dataset;
use sp_runtime::traits::OnRuntimeUpgrade;

#[test]
fn upgrade_works() {
    ExtBuilder::default().build().execute_with(|| {
        start_era(3);

        assert_eq!(Session::validators(), vec![21, 11]);

        // Insert fake data to check the migration
        put_storage_value::<Vec<AccountId>>(b"Staking", b"CurrentElected", b"", vec![21, 31]);
        put_storage_value::<SessionIndex>(b"Staking", b"CurrentEraStartSessionIndex", b"", 5);
        put_storage_value::<MomentOf<Test>>(b"Staking", b"CurrentEraStart", b"", 777);
        put_storage_value(
            b"Staking", b"Stakers", &blake2_256(&11u64.encode()),
            Exposure::<AccountId, Balance> {
                total: 10,
                own: 10,
                others: vec![],
            }
        );
        put_storage_value(
            b"Staking", b"Stakers", &blake2_256(&21u64.encode()),
            Exposure::<AccountId, Balance> {
                total: 20,
                own: 20,
                others: vec![],
            }
        );
        put_storage_value(
            b"Staking", b"Stakers", &blake2_256(&31u64.encode()),
            Exposure::<AccountId, Balance> {
                total: 30,
                own: 30,
                others: vec![],
            }
        );
        put_storage_value::<(u32, Vec<u32>)>(b"Staking", b"CurrentEraPointsEarned", b"", (12, vec![2, 10]));
        <Staking as Store>::ErasStakers::remove_all();
        <Staking as Store>::ErasStakersClipped::remove_all();

        <Staking as Store>::StorageVersion::put(Releases::V1_0_0);

        // Perform upgrade
        Staking::on_runtime_upgrade();

        assert_eq!(<Staking as Store>::StorageVersion::get(), Releases::V2_0_0);

        // Check migration
        assert_eq!(<Staking as Store>::ErasStartSessionIndex::get(3).unwrap(), 5);
        assert_eq!(<Staking as Store>::ErasRewardPoints::get(3), EraRewardPoints {
            total: 12,
            individual: vec![(21, 2), (31, 10)].into_iter().collect(),
        });
        assert_eq!(<Staking as Store>::ActiveEra::get().unwrap().index, 3);
        assert_eq!(<Staking as Store>::ActiveEra::get().unwrap().start, Some(777));
        assert_eq!(<Staking as Store>::CurrentEra::get().unwrap(), 3);
        assert_eq!(<Staking as Store>::ErasStakers::get(3, 11), Exposure {
            total: 0,
            own: 0,
            others: vec![],
        });
        assert_eq!(<Staking as Store>::ErasStakers::get(3, 21), Exposure {
            total: 20,
            own: 20,
            others: vec![],
        });
        assert_eq!(<Staking as Store>::ErasStakers::get(3, 31), Exposure {
            total: 30,
            own: 30,
            others: vec![],
        });
        assert_eq!(<Staking as Store>::ErasStakersClipped::get(3, 11), Exposure {
            total: 0,
            own: 0,
            others: vec![],
        });
        assert_eq!(<Staking as Store>::ErasStakersClipped::get(3, 21), Exposure {
            total: 20,
            own: 20,
            others: vec![],
        });
        assert_eq!(<Staking as Store>::ErasStakersClipped::get(3, 31), Exposure {
            total: 30,
            own: 30,
            others: vec![],
        });
        assert_eq!(<Staking as Store>::ErasValidatorPrefs::get(3, 21), Staking::validators(21));
        assert_eq!(<Staking as Store>::ErasValidatorPrefs::get(3, 31), Staking::validators(31));
        assert_eq!(<Staking as Store>::ErasTotalStake::get(3), 50);
    })
}

// Test that an upgrade from previous test environment works.
#[test]
fn test_upgrade_from_master_works() {
    let data_sets = &[
        test_upgrade_from_master_dataset::_0,
        test_upgrade_from_master_dataset::_1,
        test_upgrade_from_master_dataset::_2,
        test_upgrade_from_master_dataset::_3,
        test_upgrade_from_master_dataset::_4,
        test_upgrade_from_master_dataset::_5,
        test_upgrade_from_master_dataset::_6,
        test_upgrade_from_master_dataset::_7,
        test_upgrade_from_master_dataset::_8,
    ];
    for data_set in data_sets.iter() {
        let mut storage = sp_runtime::Storage::default();
        for (key, value) in data_set.iter() {
            storage.top.insert(key.to_vec(), value.to_vec());
        }
        let mut ext = sp_io::TestExternalities::from(storage);
        ext.execute_with(|| {
            let old_stakers =
                get_storage_value::<Vec<AccountId>>(b"Staking", b"CurrentElected", b"").unwrap();
            let old_staker_0 = old_stakers[0];
            let old_staker_1 = old_stakers[1];
            let old_current_era =
                get_storage_value::<EraIndex>(b"Staking", b"CurrentEra", b"").unwrap();
            let old_staker_0_exposure = get_storage_value::<Exposure<AccountId, Balance>>(
                b"Staking", b"Stakers", &blake2_256(&old_staker_0.encode())
            ).unwrap();
            let old_staker_1_exposure = get_storage_value::<Exposure<AccountId, Balance>>(
                b"Staking", b"Stakers", &blake2_256(&old_staker_1.encode())
            ).unwrap();
            let (
                old_era_points_earned_total,
                old_era_points_earned_individual
            ) = get_storage_value::<(u32, Vec<u32>)>(b"Staking", b"CurrentEraPointsEarned", b"")
                .unwrap_or((0, vec![]));

            Staking::on_runtime_upgrade();
            assert!(<Staking as Store>::StorageVersion::get() == Releases::V2_0_0);

            // Check ActiveEra and CurrentEra
            let active_era = Staking::active_era().unwrap().index;
            let current_era = Staking::current_era().unwrap();
            assert!(current_era == active_era);
            assert!(current_era == old_current_era);

            // Check ErasStartSessionIndex
            let active_era_start = Staking::eras_start_session_index(active_era).unwrap();
            let current_era_start = Staking::eras_start_session_index(current_era).unwrap();
            let current_session_index = Session::current_index();
            assert!(current_era_start == active_era_start);
            assert!(active_era_start <= current_session_index);
            assert_eq!(<Staking as Store>::ErasStartSessionIndex::iter().count(), 1);

            // Check ErasStakers
            assert_eq!(<Staking as Store>::ErasStakers::iter().count(), 2);
            assert_eq!(
                <Staking as Store>::ErasStakers::get(current_era, old_staker_0),
                old_staker_0_exposure
            );
            assert_eq!(
                <Staking as Store>::ErasStakers::get(current_era, old_staker_1),
                old_staker_1_exposure
            );

            // Check ErasStakersClipped
            assert_eq!(<Staking as Store>::ErasStakersClipped::iter().count(), 2);
            assert!(<Staking as Store>::ErasStakersClipped::iter().all(|exposure_clipped| {
                let max = <Test as Trait>::MaxNominatorRewardedPerValidator::get() as usize;
                exposure_clipped.others.len() <= max
            }));
            assert_eq!(
                <Staking as Store>::ErasStakersClipped::get(current_era, old_staker_0),
                old_staker_0_exposure
            );
            assert_eq!(
                <Staking as Store>::ErasStakersClipped::get(current_era, old_staker_1),
                old_staker_1_exposure
            );

            // Check ErasValidatorPrefs
            assert_eq!(<Staking as Store>::ErasValidatorPrefs::iter().count(), 2);
            assert_eq!(
                <Staking as Store>::ErasValidatorPrefs::get(current_era, old_staker_0),
                Staking::validators(old_staker_0)
            );
            assert_eq!(
                <Staking as Store>::ErasValidatorPrefs::get(current_era, old_staker_1),
                Staking::validators(old_staker_1)
            );

            // Check ErasTotalStake
            assert_eq!(<Staking as Store>::ErasTotalStake::iter().count(), 1);
            assert_eq!(
                <Staking as Store>::ErasTotalStake::get(current_era),
                old_staker_0_exposure.total + old_staker_1_exposure.total
            );

            // Check ErasRewardPoints
            assert_eq!(<Staking as Store>::ErasRewardPoints::iter().count(), 1);
            let mut individual = BTreeMap::new();
            if let Some(p) = old_era_points_earned_individual.get(0) {
                individual.insert(old_staker_0, p.clone());
            }
            if let Some(p) = old_era_points_earned_individual.get(1) {
                individual.insert(old_staker_1, p.clone());
            }
            assert_eq!(
                <Staking as Store>::ErasRewardPoints::get(current_era),
                EraRewardPoints {
                    total: old_era_points_earned_total,
                    individual,
                }
            );

            // Check ErasValidatorReward
            assert_eq!(<Staking as Store>::ErasValidatorReward::iter().count(), 0);
        });
    }
}
