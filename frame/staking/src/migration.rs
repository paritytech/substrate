use super::*;

use frame_support::weights::Weight;

/// Deprecated storages used for migration only.
mod deprecated {
    use crate::{BalanceOf, Exposure, SessionIndex, Trait};
    use codec::{Decode, Encode};
    use frame_support::{decl_module, decl_storage};
    use sp_std::prelude::*;

    // edgeware uses `u64` for `Moment`
    pub type Moment = u64;

    /// Reward points of an era. Used to split era total payout between validators.
    #[derive(Encode, Decode, Default)]
    pub struct EraPoints {
        /// Total number of points. Equals the sum of reward points for each validator.
        pub total: u32,
        /// The reward points earned by a given validator. The index of this vec corresponds to the
        /// index into the current validator set.
        pub individual: Vec<u32>,
    }

    decl_module! {
        pub struct Module<T: Trait> for enum Call where origin: T::Origin { }
    }

    decl_storage! {
        pub trait Store for Module<T: Trait> as Staking {
            pub SlotStake: BalanceOf<T>;

            /// The currently elected validator set keyed by stash account ID.
            pub CurrentElected: Vec<T::AccountId>;

            /// The start of the current era.
            pub CurrentEraStart: Moment;

            /// The session index at which the current era started.
            pub CurrentEraStartSessionIndex: SessionIndex;

            /// Rewards for the current era. Using indices of current elected set.
            pub CurrentEraPointsEarned: EraPoints;

            /// Nominators for a particular account that is in action right now. You can't iterate
            /// through validators here, but you can find them in the Session module.
            ///
            /// This is keyed by the stash account.
            pub Stakers: map hasher(opaque_blake2_256) T::AccountId => Exposure<T::AccountId, BalanceOf<T>>;

            pub StorageVersion: u32;
        }
    }
}

#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
struct OldStakingLedger<AccountId, Balance: HasCompact> {
    pub stash: AccountId,
    #[codec(compact)]
    pub total: Balance,
    #[codec(compact)]
    pub active: Balance,
    pub unlocking: Vec<UnlockChunk<Balance>>,
}

/// Update storages to current version
///
/// In old version the staking module has several issue about handling session delay, the
/// current era was always considered the active one.
///
/// After the migration the current era will still be considered the active one for the era of
/// the upgrade. And the delay issue will be fixed when planning the next era.
// * create:
//   * ActiveEraStart
//   * ErasRewardPoints
//   * ActiveEra
//   * ErasStakers
//   * ErasStakersClipped
//   * ErasValidatorPrefs
//   * ErasTotalStake
//   * ErasStartSessionIndex
// * translate StakingLedger
// * removal of:
//   * Stakers
//   * SlotStake
//   * CurrentElected
//   * CurrentEraStart
//   * CurrentEraStartSessionIndex
//   * CurrentEraPointsEarned
//
// The edgeware migration is so big we just assume it consumes the whole block.
pub fn migrate_to_simple_payouts<T: Trait>() -> Weight {
    let version = deprecated::StorageVersion::take();
    if version != 2 {
        frame_support::runtime_print!("🕊️  Unexpected Staking StorageVersion: {}", version);
        return 0;
    }
    sp_runtime::print("🕊️  Migrating Staking...");
    let current_era_start_index = deprecated::CurrentEraStartSessionIndex::get();
    let current_era = <Module<T> as Store>::CurrentEra::get().unwrap_or(0);
    let current_era_start = deprecated::CurrentEraStart::get();
    <Module<T> as Store>::ErasStartSessionIndex::insert(current_era, current_era_start_index);
    <Module<T> as Store>::ActiveEra::put(ActiveEraInfo {
        index: current_era,
        start: Some(current_era_start),
    });

    let current_elected = deprecated::CurrentElected::<T>::get();
    let mut current_total_stake = <BalanceOf<T>>::zero();
    for validator in &current_elected {
        let exposure = deprecated::Stakers::<T>::get(validator);
        current_total_stake += exposure.total;
        <Module<T> as Store>::ErasStakers::insert(current_era, validator, &exposure);

        let mut exposure_clipped = exposure;
        let clipped_max_len = T::MaxNominatorRewardedPerValidator::get() as usize;
        if exposure_clipped.others.len() > clipped_max_len {
            exposure_clipped
                .others
                .sort_unstable_by(|a, b| a.value.cmp(&b.value).reverse());
            exposure_clipped.others.truncate(clipped_max_len);
        }
        <Module<T> as Store>::ErasStakersClipped::insert(current_era, validator, exposure_clipped);

        let pref = <Module<T> as Store>::Validators::get(validator);
        <Module<T> as Store>::ErasValidatorPrefs::insert(current_era, validator, pref);
    }
    <Module<T> as Store>::ErasTotalStake::insert(current_era, current_total_stake);

    let points = deprecated::CurrentEraPointsEarned::get();
    <Module<T> as Store>::ErasRewardPoints::insert(
        current_era,
        EraRewardPoints {
            total: points.total,
            individual: current_elected
                .iter()
                .cloned()
                .zip(points.individual.iter().cloned())
                .collect(),
        },
    );

    let res = <Module<T> as Store>::Ledger::translate_values(
        |old: OldStakingLedger<T::AccountId, BalanceOf<T>>| StakingLedger {
            stash: old.stash,
            total: old.total,
            active: old.active,
            unlocking: old.unlocking,
            claimed_rewards: vec![],
        },
    );
    if let Err(e) = res {
        frame_support::print("Encountered error in migration of Staking::Ledger map.");
        frame_support::print("The number of removed key/value is:");
        frame_support::print(e);
    }

    // Kill old storages
    deprecated::Stakers::<T>::remove_all();
    deprecated::SlotStake::<T>::kill();
    deprecated::CurrentElected::<T>::kill();
    deprecated::CurrentEraStart::kill();
    deprecated::CurrentEraStartSessionIndex::kill();
    deprecated::CurrentEraPointsEarned::kill();

    StorageVersion::put(Releases::V4_0_0);

    sp_runtime::print("🕊️  Done Staking.");
    T::MaximumBlockWeight::get()
}
