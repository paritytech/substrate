pub(crate) const LOG_TARGET: &str = "runtime::stake-tracker";

#[macro_export]
macro_rules! log {
	($level:tt, $patter:expr $(, $values:expr)* $(,)?) => {
		log::$level!(
			target: crate::LOG_TARGET,
			concat!("💸🧐", $patter), $(, $values)*
		)
	};
}

pub mod v2 {}
//TODO: Introduce try-state to the pallet
//TODO: Decide what to do with new networks, no harm done if this is run on an empty Staking
// storage
pub mod v1 {
	use codec::{Decode, Encode};
	use frame_election_provider_support::SortedListProvider;
	use frame_support::{
		pallet_prelude::*, sp_io, storage_alias, traits::OnRuntimeUpgrade, CloneNoBound, EqNoBound,
		PartialEqNoBound,
	};
	use pallet_stake_tracker::{ApprovalStake, BalanceOf, Pallet};
	use pallet_staking::{Nominations, Nominators, Validators};
	use sp_runtime::Saturating;
	use std::collections::BTreeMap;

	/// Migration implementation that injects all validators into sorted list.
	pub struct InjectValidatorsApprovalStakeIntoTargetList<T>(PhantomData<T>);

	#[derive(Encode, Decode, CloneNoBound, PartialEqNoBound, EqNoBound, Default)]
	#[codec(mel_bound())]
	pub struct MigrationState {
		pub last_key: Vec<u8>,
		pub prefix: Vec<u8>,
		pub done: bool,
	}

	#[storage_alias]
	type MigrationV1StateNominators<T: pallet_staking::Config + pallet_stake_tracker::Config> =
		StorageValue<Pallet<T>, MigrationState, OptionQuery>;

	#[storage_alias]
	type MigrationV1StateValidators<T: pallet_staking::Config + pallet_stake_tracker::Config> =
		StorageValue<Pallet<T>, MigrationState, OptionQuery>;

	impl<T: pallet_staking::Config + pallet_stake_tracker::Config>
		InjectValidatorsApprovalStakeIntoTargetList<T>
	{
		fn nominator_state() -> MigrationState {
			MigrationV1StateNominators::<T>::get().unwrap_or(MigrationState {
				last_key: <pallet_staking::Nominators<T>>::map_storage_final_prefix(),
				prefix: <pallet_staking::Nominators<T>>::map_storage_final_prefix(),
				done: false,
			})
		}

		fn set_nominator_state(state: MigrationState) {
			MigrationV1StateNominators::<T>::set(Some(state))
		}

		fn validator_state() -> MigrationState {
			MigrationV1StateValidators::<T>::get().unwrap_or(MigrationState {
				last_key: <pallet_staking::Nominators<T>>::map_storage_final_prefix(),
				prefix: <pallet_staking::Nominators<T>>::map_storage_final_prefix(),
				done: false,
			})
		}

		fn set_validator_state(state: MigrationState) {
			MigrationV1StateValidators::<T>::set(Some(state))
		}

		pub(crate) fn build_approval_stakes(
			max_iterations: Weight,
		) -> (BTreeMap<T::AccountId, BalanceOf<T>>, Weight) {
			let mut iterations: Weight = Weight::default();
			let mut approval_stakes = BTreeMap::<T::AccountId, BalanceOf<T>>::new();
			let mut leftover_weight = T::BlockWeights::get().max_block;

			let mut nominator_state = Self::nominator_state();

			if !nominator_state.done {
				// each iteration = 2 reads + 2 reads = 4 reads
				while let Some(next_key) =
					sp_io::storage::next_key(nominator_state.last_key.as_ref())
				{
					if !next_key.starts_with(&nominator_state.prefix) {
						// Nothing else to iterate. Save the state and bail.
						nominator_state.done = true;
						Self::set_nominator_state(nominator_state.clone());
						break
					}

					// Should be safe due to the check above.
					let mut account_raw =
						next_key.strip_prefix(nominator_state.prefix.as_slice()).unwrap();
					let who = T::AccountId::decode(&mut account_raw).unwrap();

					match storage::unhashed::get::<Nominations<T>>(&next_key) {
						Some(nominations) => {
							let stake = Pallet::<T>::slashable_balance_of(&who);

							for target in nominations.targets {
								let current = approval_stakes.entry(target).or_default();
								*current = current.saturating_add(stake);
							}

							iterations = iterations.saturating_add(Weight::from_ref_time(1));
							nominator_state.last_key = next_key;
							leftover_weight =
								max_iterations.saturating_sub(iterations).saturating_sub(
									Weight::from_ref_time(approval_stakes.len() as u64),
								);

							if leftover_weight.all_lte(Weight::default()) {
								// We ran out of weight, also taking into account writing
								// approval_stakes here. Save the state and bail.
								Self::set_nominator_state(nominator_state.clone());

								return (approval_stakes, leftover_weight)
							}
						},
						None => {
							log!(warn, "an un-decodable nomination detected.");
							break
						},
					};
				}
			}

			let mut validator_state = Self::validator_state();

			if !validator_state.done {
				// each iteration = 1 read + 2 reads = 3 reads
				while let Some(next_key) =
					sp_io::storage::next_key(validator_state.last_key.as_ref())
				{
					if !next_key.starts_with(&validator_state.prefix) {
						// Nothing else to iterate. Save the state and bail.
						validator_state.done = true;
						Self::set_validator_state(validator_state.clone());
						break
					}

					// Should be safe due to the check above.
					let mut account_raw =
						next_key.strip_prefix(validator_state.prefix.as_slice()).unwrap();

					// TODO: not sure if this works, gotta see. Should be safe as all the keys in
					// Validators map are AccountId. If not - let it fail.
					let who = T::AccountId::decode(&mut account_raw).unwrap();
					let stake = Pallet::<T>::slashable_balance_of(&who);
					let current = approval_stakes.entry(who).or_default();
					*current = current.saturating_add(stake);
					iterations = iterations.saturating_add(Weight::from_ref_time(1));
					validator_state.last_key = next_key;

					leftover_weight = max_iterations
						.saturating_sub(iterations)
						.saturating_sub(Weight::from_ref_time(approval_stakes.len() as u64));

					if leftover_weight.all_lte(Weight::default()) {
						// We ran out of weight, also taking into account writing
						// approval_stakes here. Save the state and bail.
						Self::set_validator_state(validator_state.clone());

						return (approval_stakes, leftover_weight)
					}
				}
			}

			(approval_stakes, leftover_weight)
		}
	}

	impl<T: pallet_staking::Config + pallet_stake_tracker::Config> OnRuntimeUpgrade
		for InjectValidatorsApprovalStakeIntoTargetList<T>
	{
		fn on_runtime_upgrade() -> Weight {
			// We have to set this manually, because we need this migration to happen in order for
			// the pallet to get all the data from staking-pallet.
			let current = StorageVersion::new(1);
			let onchain = Pallet::<T>::on_chain_storage_version();

			if current == 1 && onchain == 0 {
				let max_weight = T::BlockWeights::get().max_block;
				// this is an approximation
				let max_iterations = max_weight.saturating_div(4);
				// TODO: maybe write this in a multi-block fashion.
				let (approval_stakes, leftover_weight) =
					Self::build_approval_stakes(max_iterations);

				for (who, approval_stake) in approval_stakes {
					if ApprovalStake::<T>::contains_key(&who) {
						ApprovalStake::<T>::mutate(&who, |maybe_stake| {
							if let Some(stake) = maybe_stake {
								stake.saturating_add(approval_stake);
							}
						})
					} else {
						ApprovalStake::<T>::insert(&who, approval_stake)
					}
				}

				if leftover_weight
					.all_gte(Weight::from_ref_time((ApprovalStake::<T>::count() * 2) as u64)) ||
					leftover_weight == max_weight
				{
					for (key, value) in ApprovalStake::<T>::iter() {
						<T as pallet_stake_tracker::Config>::TargetList::on_insert(key, value)
							.unwrap();
					}
				}

				current.put::<Pallet<T>>();
				max_weight
			} else {
				log!(warn, "This migration is being executed on a wrong storage version, probably needs to be removed.");
				T::DbWeight::get().reads(1)
			}
		}

		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<(), &'static str> {
			ensure!(StorageVersion::<T>::get() == "0", "must upgrade linearly");
			Ok(())
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade() -> Result<(), &'static str> {
			ensure!(StorageVersion::<T>::get() == "1", "must upgrade linearly");
			Ok(())
		}
	}
}
