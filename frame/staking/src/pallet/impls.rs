// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Implementations for the Staking FRAME Pallet.

use frame_election_provider_support::{
	data_provider, BoundedSupportsOf, ElectionDataProvider, ElectionProvider, ExtendedBalance,
	PageIndex, ScoreProvider, SortedListProvider, VoteWeight, VoterOf,
};
use frame_support::{
	pallet_prelude::*,
	traits::{
		Currency, CurrencyToVote, Defensive, EstimateNextNewSession, Get, Imbalance,
		LockableCurrency, OnUnbalanced, TryCollect, UnixTime, WithdrawReasons,
	},
	weights::{Weight, WithPostDispatchInfo},
};
use frame_system::pallet_prelude::BlockNumberFor;
use pallet_session::historical;
use sp_runtime::{
	traits::{Bounded, Convert, SaturatedConversion, Saturating, Zero},
	Perbill,
};
use sp_staking::{
	offence::{DisableStrategy, OffenceDetails, OnOffenceHandler},
	EraIndex, SessionIndex,
};
use sp_std::{collections::btree_map::BTreeMap, prelude::*};

use crate::{
	log, slashing, weights::WeightInfo, ActiveEraInfo, BalanceOf, EraPayout, Exposure, ExposureOf,
	Forcing, IndividualExposure, MaxExposuresPerPageOf, MaxIndividualExposuresOf, Nominations,
	PagesOf, PositiveImbalanceOf, RewardDestination, SessionInterface, StakingLedger,
	ValidatorPrefs,
};

use super::{pallet::*, STAKING_ID};

impl<T: Config> Pallet<T> {
	/// The total balance that can be slashed from a stash account as of right now.
	pub fn slashable_balance_of(stash: &T::AccountId) -> BalanceOf<T> {
		// Weight note: consider making the stake accessible through stash.
		Self::bonded(stash).and_then(Self::ledger).map(|l| l.active).unwrap_or_default()
	}

	/// Internal impl of [`Self::slashable_balance_of`] that returns [`VoteWeight`].
	pub fn slashable_balance_of_vote_weight(
		stash: &T::AccountId,
		issuance: BalanceOf<T>,
	) -> VoteWeight {
		T::CurrencyToVote::to_vote(Self::slashable_balance_of(stash), issuance)
	}

	/// Returns a closure around `slashable_balance_of_vote_weight` that can be passed around.
	///
	/// This prevents call sites from repeatedly requesting `total_issuance` from backend. But it is
	/// important to be only used while the total issuance is not changing.
	pub fn weight_of_fn() -> Box<dyn Fn(&T::AccountId) -> VoteWeight> {
		// NOTE: changing this to unboxed `impl Fn(..)` return type and the pallet will still
		// compile, while some types in mock fail to resolve.
		let issuance = T::Currency::total_issuance();
		Box::new(move |who: &T::AccountId| -> VoteWeight {
			Self::slashable_balance_of_vote_weight(who, issuance)
		})
	}

	/// Same as `weight_of_fn`, but made for one time use.
	pub fn weight_of(who: &T::AccountId) -> VoteWeight {
		let issuance = T::Currency::total_issuance();
		Self::slashable_balance_of_vote_weight(who, issuance)
	}

	pub(super) fn do_payout_stakers(
		validator_stash: T::AccountId,
		era: EraIndex,
	) -> DispatchResultWithPostInfo {
		// Validate input data
		let current_era = CurrentEra::<T>::get().ok_or_else(|| {
			Error::<T>::InvalidEraToReward
				.with_weight(T::WeightInfo::payout_stakers_alive_staked(0))
		})?;
		let history_depth = Self::history_depth();
		ensure!(
			era <= current_era && era >= current_era.saturating_sub(history_depth),
			Error::<T>::InvalidEraToReward
				.with_weight(T::WeightInfo::payout_stakers_alive_staked(0))
		);

		// Note: if era has no reward to be claimed, era may be future. better not to update
		// `ledger.claimed_rewards` in this case.
		let era_payout = <ErasValidatorReward<T>>::get(&era).ok_or_else(|| {
			Error::<T>::InvalidEraToReward
				.with_weight(T::WeightInfo::payout_stakers_alive_staked(0))
		})?;

		let controller = Self::bonded(&validator_stash).ok_or_else(|| {
			Error::<T>::NotStash.with_weight(T::WeightInfo::payout_stakers_alive_staked(0))
		})?;
		let mut ledger = <Ledger<T>>::get(&controller).ok_or(Error::<T>::NotController)?;

		ledger
			.claimed_rewards
			.retain(|&x| x >= current_era.saturating_sub(history_depth));
		match ledger.claimed_rewards.binary_search(&era) {
			Ok(_) => Err(Error::<T>::AlreadyClaimed
				.with_weight(T::WeightInfo::payout_stakers_alive_staked(0)))?,
			Err(pos) => ledger.claimed_rewards.insert(pos, era),
		}

		let exposure = <ErasStakersClipped<T>>::get(&era, &ledger.stash);

		// Input data seems good, no errors allowed after this point

		<Ledger<T>>::insert(&controller, &ledger);

		// Get Era reward points. It has TOTAL and INDIVIDUAL
		// Find the fraction of the era reward that belongs to the validator
		// Take that fraction of the eras rewards to split to nominator and validator
		//
		// Then look at the validator, figure out the proportion of their reward
		// which goes to them and each of their nominators.

		let era_reward_points = <ErasRewardPoints<T>>::get(&era);
		let total_reward_points = era_reward_points.total;
		let validator_reward_points = era_reward_points
			.individual
			.get(&ledger.stash)
			.map(|points| *points)
			.unwrap_or_else(|| Zero::zero());

		// Nothing to do if they have no reward points.
		if validator_reward_points.is_zero() {
			return Ok(Some(T::WeightInfo::payout_stakers_alive_staked(0)).into())
		}

		// This is the fraction of the total reward that the validator and the
		// nominators will get.
		let validator_total_reward_part =
			Perbill::from_rational(validator_reward_points, total_reward_points);

		// This is how much validator + nominators are entitled to.
		let validator_total_payout = validator_total_reward_part * era_payout;

		let validator_prefs = Self::eras_validator_prefs(&era, &validator_stash);
		// Validator first gets a cut off the top.
		let validator_commission = validator_prefs.commission;
		let validator_commission_payout = validator_commission * validator_total_payout;

		let validator_leftover_payout = validator_total_payout - validator_commission_payout;
		// Now let's calculate how this is split to the validator.
		let validator_exposure_part = Perbill::from_rational(exposure.own, exposure.total);
		let validator_staking_payout = validator_exposure_part * validator_leftover_payout;

		Self::deposit_event(Event::<T>::PayoutStarted(era, ledger.stash.clone()));

		// We can now make total validator payout:
		if let Some(imbalance) =
			Self::make_payout(&ledger.stash, validator_staking_payout + validator_commission_payout)
		{
			Self::deposit_event(Event::<T>::Rewarded(ledger.stash, imbalance.peek()));
		}

		// Track the number of payout ops to nominators. Note:
		// `WeightInfo::payout_stakers_alive_staked` always assumes at least a validator is paid
		// out, so we do not need to count their payout op.
		let mut nominator_payout_count: u32 = 0;

		// Lets now calculate how this is split to the nominators.
		// Reward only the clipped exposures. Note this is not necessarily sorted.
		for nominator in exposure.others.iter() {
			let nominator_exposure_part = Perbill::from_rational(nominator.value, exposure.total);

			let nominator_reward: BalanceOf<T> =
				nominator_exposure_part * validator_leftover_payout;
			// We can now make nominator payout:
			if let Some(imbalance) = Self::make_payout(&nominator.who, nominator_reward) {
				// Note: this logic does not count payouts for `RewardDestination::None`.
				nominator_payout_count += 1;
				let e = Event::<T>::Rewarded(nominator.who.clone(), imbalance.peek());
				Self::deposit_event(e);
			}
		}

		debug_assert!(nominator_payout_count <= T::MaxNominatorRewardedPerValidator::get());
		Ok(Some(T::WeightInfo::payout_stakers_alive_staked(nominator_payout_count)).into())
	}

	/// Update the ledger for a controller.
	///
	/// This will also update the stash lock.
	pub(crate) fn update_ledger(
		controller: &T::AccountId,
		ledger: &StakingLedger<T::AccountId, BalanceOf<T>>,
	) {
		T::Currency::set_lock(STAKING_ID, &ledger.stash, ledger.total, WithdrawReasons::all());
		<Ledger<T>>::insert(controller, ledger);
	}

	/// Chill a stash account.
	pub(crate) fn chill_stash(stash: &T::AccountId) {
		let chilled_as_validator = Self::do_remove_validator(stash);
		let chilled_as_nominator = Self::do_remove_nominator(stash);
		if chilled_as_validator || chilled_as_nominator {
			Self::deposit_event(Event::<T>::Chilled(stash.clone()));
		}
	}

	/// Actually make a payment to a staker. This uses the currency's reward function
	/// to pay the right payee for the given staker account.
	fn make_payout(stash: &T::AccountId, amount: BalanceOf<T>) -> Option<PositiveImbalanceOf<T>> {
		let dest = Self::payee(stash);
		match dest {
			RewardDestination::Controller => Self::bonded(stash)
				.map(|controller| T::Currency::deposit_creating(&controller, amount)),
			RewardDestination::Stash => T::Currency::deposit_into_existing(stash, amount).ok(),
			RewardDestination::Staked => Self::bonded(stash)
				.and_then(|c| Self::ledger(&c).map(|l| (c, l)))
				.and_then(|(controller, mut l)| {
					l.active += amount;
					l.total += amount;
					let r = T::Currency::deposit_into_existing(stash, amount).ok();
					Self::update_ledger(&controller, &l);
					r
				}),
			RewardDestination::Account(dest_account) =>
				Some(T::Currency::deposit_creating(&dest_account, amount)),
			RewardDestination::None => None,
		}
	}

	/// Plan a new session potentially trigger a new era.
	fn new_session(session_index: SessionIndex, is_genesis: bool) -> Option<Vec<T::AccountId>> {
		if let Some(current_era) = Self::current_era() {
			// Initial era has been set.
			let current_era_start_session_index = Self::eras_start_session_index(current_era)
				.unwrap_or_else(|| {
					frame_support::print("Error: start_session_index must be set for current_era");
					0
				});

			let era_length =
				session_index.checked_sub(current_era_start_session_index).unwrap_or(0); // Must never happen.

			match ForceEra::<T>::get() {
				// Will be set to `NotForcing` again if a new era has been triggered.
				Forcing::ForceNew => (),
				// Short circuit to `try_trigger_new_era`.
				Forcing::ForceAlways => (),
				// Only go to `try_trigger_new_era` if deadline reached.
				Forcing::NotForcing if era_length >= T::SessionsPerEra::get() => (),
				_ => {
					// Either `Forcing::ForceNone`,
					// or `Forcing::NotForcing if era_length >= T::SessionsPerEra::get()`.
					return None
				},
			}

			// New era.
			let maybe_new_era_validators = Self::try_trigger_new_pending_era(
				current_era.saturating_add(1),
				session_index,
				is_genesis,
			);
			if maybe_new_era_validators.is_some() &&
				matches!(ForceEra::<T>::get(), Forcing::ForceNew)
			{
				ForceEra::<T>::put(Forcing::NotForcing);
			}

			maybe_new_era_validators
		} else {
			Self::try_trigger_new_pending_era(0, session_index, is_genesis)
		}
	}

	/// Start a session potentially starting an era.
	fn start_session(start_session: SessionIndex) {
		let next_active_era = Self::active_era().map(|e| e.index + 1).unwrap_or(0);
		// This is only `Some` when current era has already progressed to the next era, while the
		// active era is one behind (i.e. in the *last session of the active era*, or *first session
		// of the new current era*, depending on how you look at it).
		if let Some(next_active_era_start_session_index) =
			Self::eras_start_session_index(next_active_era)
		{
			if next_active_era_start_session_index == start_session {
				Self::start_era(start_session);
			} else if next_active_era_start_session_index < start_session {
				// This arm should never happen, but better handle it than to stall the staking
				// pallet.
				frame_support::print("Warning: A session appears to have been skipped.");
				Self::start_era(start_session);
			}
		}

		// disable all offending validators that have been disabled for the whole era
		for (index, disabled) in <OffendingValidators<T>>::get() {
			if disabled {
				T::SessionInterface::disable_validator(index);
			}
		}
	}

	/// End a session potentially ending an era.
	fn end_session(session_index: SessionIndex) {
		if let Some(active_era) = Self::active_era() {
			if let Some(next_active_era_start_session_index) =
				Self::eras_start_session_index(active_era.index + 1)
			{
				if next_active_era_start_session_index == session_index + 1 {
					Self::end_era(active_era, session_index);
				}
			}
		}
	}

	///
	/// * Increment `active_era.index`,
	/// * reset `active_era.start`,
	/// * update `BondedEras` and apply slashes.
	fn start_era(start_session: SessionIndex) {
		let active_era = ActiveEra::<T>::mutate(|active_era| {
			let new_index = active_era.as_ref().map(|info| info.index + 1).unwrap_or(0);
			*active_era = Some(ActiveEraInfo {
				index: new_index,
				// Set new active era start in next `on_finalize`. To guarantee usage of `Time`
				start: None,
			});
			new_index
		});

		let bonding_duration = T::BondingDuration::get();

		BondedEras::<T>::mutate(|bonded| {
			bonded.push((active_era, start_session));

			if active_era > bonding_duration {
				let first_kept = active_era - bonding_duration;

				// Prune out everything that's from before the first-kept index.
				let n_to_prune =
					bonded.iter().take_while(|&&(era_idx, _)| era_idx < first_kept).count();

				// Kill slashing metadata.
				for (pruned_era, _) in bonded.drain(..n_to_prune) {
					slashing::clear_era_metadata::<T>(pruned_era);
				}

				if let Some(&(_, first_session)) = bonded.first() {
					T::SessionInterface::prune_historical_up_to(first_session);
				}
			}
		});

		Self::apply_unapplied_slashes(active_era);
	}

	/// Compute payout for era.
	fn end_era(active_era: ActiveEraInfo, _session_index: SessionIndex) {
		// Note: active_era_start can be None if end era is called during genesis config.
		if let Some(active_era_start) = active_era.start {
			let now_as_millis_u64 = T::UnixTime::now().as_millis().saturated_into::<u64>();

			let era_duration = (now_as_millis_u64 - active_era_start).saturated_into::<u64>();
			let staked = Self::eras_total_stake(&active_era.index);
			let issuance = T::Currency::total_issuance();
			let (validator_payout, rest) = T::EraPayout::era_payout(staked, issuance, era_duration);

			Self::deposit_event(Event::<T>::EraPaid(active_era.index, validator_payout, rest));

			// Set ending era reward.
			<ErasValidatorReward<T>>::insert(&active_era.index, validator_payout);
			T::RewardRemainder::on_unbalanced(T::Currency::issue(rest));

			// Clear offending validators.
			<OffendingValidators<T>>::kill();
		}
	}

	/// Plan a new era.
	///
	/// * Set the CurrentEra to the given staring era. This should almost always be the previous
	///   one, plus one.
	/// * Store start session index for the new planned era.
	/// * Clean old era information.
	/// * Store staking information for the new planned era
	///
	/// Returns the new validator set.
	pub fn trigger_new_era(starting_era: EraIndex, start_session_index: SessionIndex) {
		// Increment or set current era.
		debug_assert!(
			Self::current_era()
				.map_or_else(|| starting_era == 0, |prev_era| prev_era + 1 == starting_era),
			"Eras not being incremented sequentially, prev {:?}, now {}.",
			Self::current_era(),
			starting_era,
		);
		CurrentEra::<T>::set(Some(starting_era));
		ErasStartSessionIndex::<T>::insert(&starting_era, &start_session_index);

		// Clean old era information.
		if let Some(old_era) = starting_era.checked_sub(Self::history_depth() + 1) {
			Self::clear_era_information(old_era);
		}
	}

	/// Potentially trigger a new era, using the pending era validator information that should have
	/// already been stored in `<NextValidators>`.
	///
	/// If `NextValidators` is empty, ElectionProvider::elect(0) is used as last resort fallback.
	///
	/// If `is_genesis` is true, then `GenesisElectionProvider` is used.
	///
	/// In case election result has more than [`MinimumValidatorCount`] validators, a new era is
	/// triggered and the new validators are returned.
	pub(crate) fn try_trigger_new_pending_era(
		maybe_starting_era: EraIndex,
		start_session_index: SessionIndex,
		is_genesis: bool,
	) -> Option<Vec<T::AccountId>> {
		let wipe_eras_stakers = |era: EraIndex| {
			<ErasStakers<T>>::remove_prefix(era, None);
			<ErasStakersClipped<T>>::remove_prefix(era, None);
			<ErasValidatorPrefs<T>>::remove_prefix(era, None);
			<ErasTotalStake<T>>::remove(era);
		};
		log!(
			info,
			"trying to trigger a new era {}, start session index of the current era {}, genesis? {}.",
			maybe_starting_era,
			start_session_index,
			is_genesis
		);

		let stashes =
			if is_genesis {
				T::GenesisElectionProvider::elect(0)
					.map(|supports| {
						// do everything that we do for the multi-block stuff here, in one go.
						// It is all good, this can only happen in genesis. If something is
						// about to go wrong, the chain won't even start.
						let exposures = Self::collect_page_exposures(supports);
						wipe_eras_stakers(maybe_starting_era);
						Self::store_page_staker_info(exposures, maybe_starting_era);
						Self::finalize_staker_info_collection(maybe_starting_era)
					})
					.ok()?
			} else {
				// we take the validators from `<NextValidators>`, which should have already been
				// stored and saved. Else. we do a last attempt at fetching something useful from
				// the election provider. This comes handy in tests and benchmarks, but also a
				// reasonable backup to have in production.
				<NextValidators<T>>::take().or_else(|| {
					log!(warn, "falling back to T::ElectionProvider::elect(0) instead of <NextValidators<T>>");
					T::ElectionProvider::elect(0)
						.map(|supports| {
							let exposures = Self::collect_page_exposures(supports);
							Self::store_page_staker_info(exposures, maybe_starting_era);
							Self::finalize_staker_info_collection(maybe_starting_era)
						})
						.ok()
				})?
			};

		if (stashes.len() as u32) < Self::minimum_validator_count().max(1) {
			// Session will panic if we ever return an empty validator set, thus max(1) ^^.
			log!(
				warn,
				"chain does not have enough staking candidates to operate for era {:?} ({} \
				elected, minimum {}). This will not potentially trigger a very expensive \
				cleanup operation. THIS SHOULD NOT HAPPEN FREQUENTLY.",
				CurrentEra::<T>::get(),
				stashes.len(),
				Self::minimum_validator_count(),
			);
			match CurrentEra::<T>::get() {
				None => {
					// The initial era is allowed to have no exposures.
					// In this case the SessionManager is expected to choose a sensible validator
					// set.
					// TODO: this should be simplified #8911
					CurrentEra::<T>::put(0);
					ErasStartSessionIndex::<T>::insert(&0, &start_session_index);
				},
				_ => (),
			}

			// Clear all storage items that may have bene written to during
			// `store_page_staker_info`, and `finalize_staker_info_collection`. This will be
			// expensive, but extremely rare to happen.
			log!(warn, "removing all staker data correlated with era {}", maybe_starting_era);
			wipe_eras_stakers(maybe_starting_era);
			Self::deposit_event(Event::StakingElectionFailed);
			return None
		}

		Self::deposit_event(Event::StakersElected);
		Self::trigger_new_era(maybe_starting_era, start_session_index);
		Some(stashes)
	}

	pub(crate) fn maybe_start_support_collection_for_era(
		now: T::BlockNumber,
		new_planned_era: EraIndex,
	) -> Result<bool, &'static str> {
		// returns true if this si going to be the last page.
		let maybe_proceed_next_page = |current_page: PageIndex| -> bool {
			if let Some(next_page) = current_page.checked_sub(1) {
				// we have a next page to attend to in the next block.
				NextElectPage::<T>::put(Some(next_page));
				false
			} else {
				// we seem to be done, if `NextElectPage` was set, then delete it.
				NextElectPage::<T>::kill();
				true
			}
		};

		let proceed_page = |supports: BoundedSupportsOf<T::ElectionProvider>,
		                    current_page: PageIndex| {
			let exposures = Self::collect_page_exposures(supports);
			Self::store_page_staker_info(exposures, new_planned_era);
			let is_last_page = maybe_proceed_next_page(current_page);
			if is_last_page {
				let next_validators = Self::finalize_staker_info_collection(new_planned_era);
				<NextValidators<T>>::put(Some(next_validators));
				false
			} else {
				true
			}
		};

		let did_collect = match Self::next_elect_page() {
			Some(next_page) => {
				// we're already in the middle of getting some pages, continue it.
				let supports =
					T::ElectionProvider::elect(next_page).map_err(|_| "first elect page failed")?;
				let _leftover = proceed_page(supports, next_page);
				log!(
					info,
					"[task] continuing exposure collection for era {}, next page {}, leftover? {}",
					new_planned_era,
					next_page,
					_leftover
				);
				true
			},
			None => {
				// check if it is time to start it.
				let next_election = Self::next_election_prediction(now);
				if next_election == now {
					// once we're at the block where election is expected, kickstart the process of
					// calling `elect`. Note that we don't do `<=` here for simplicity.

					let first_page = <T::ElectionProvider as ElectionProvider>::msp();
					let supports = T::ElectionProvider::elect(first_page)
						.map_err(|_| "first elect page failed")?;
					let _leftover = proceed_page(supports, first_page);
					log!(
						info,
						"[task] initiating collecting exposure for era {}, first page = {}, leftover? {}",
						new_planned_era,
						first_page,
						_leftover
					);
					true
				} else {
					false
				}
			},
		};

		Ok(did_collect)
	}

	/// Write the `exposures` for era `new_planned_era`.
	///
	/// These exposures are potentially partial, the could only correspond to one page of the
	/// election result.
	pub(crate) fn store_page_staker_info(
		exposures: BoundedVec<(T::AccountId, Exposure<T>), MaxExposuresPerPageOf<T>>,
		new_planned_era: EraIndex,
	) {
		log!(debug, "storing intermediary staker values for era {}", new_planned_era);
		let mut total_stake: BalanceOf<T> = Zero::zero();
		for (validator_stash, exposure) in exposures {
			total_stake = total_stake.saturating_add(exposure.total);

			// mix these exposures with the existing ones, if any.
			<ErasStakers<T>>::mutate(new_planned_era, validator_stash, |current_exposure| {
				(*current_exposure).total = current_exposure.total.saturating_add(exposure.total);
				// defensive-only: `own` should only ever be incremented once, not much we can do
				// about it if otherwise.
				// THIS is the root of the evil for now, if we go over a set, and then we don't have
				// enough winners, then we are kinda fucked. I think a reasonable thing to do is to,
				// for now assume that this will never happen since the election provider guarantees
				// to select enough winners. If it happens to do, then we stall the election, or
				// something else.
				debug_assert!(current_exposure.own.is_zero() || exposure.own.is_zero());
				current_exposure.own = current_exposure.own.saturating_add(exposure.own);
				let _ =
					current_exposure.others.try_extend(exposure.others.into_iter()).map_err(|_| {
						debug_assert!(false, "defensive error occurred.");
						log!(error, "defensive error occurred.")
					});
			})
		}

		// update the total_stake
		<ErasTotalStake<T>>::mutate(new_planned_era, |stake| {
			*stake = (*stake).saturating_add(total_stake);
		});
	}

	/// Take all the stakers from [`ErasStakers`], store them as [`ErasStakersClipped`]. Also,
	/// update all validators preferences and returns the final flat list of new validators, to be
	/// passed in to the session pallet in [`NextValidators`].
	///
	/// NOTE: very important weight/memory assumptions must be upheld here:
	///
	/// 1. the length of `IndividualExposure` of no staker is so much to fail the allocator.
	pub(crate) fn finalize_staker_info_collection(new_planned_era: EraIndex) -> Vec<T::AccountId> {
		// collect the elected stashes, along the way update the clipped stakers as well.
		let elected_stashes = <ErasStakers<T>>::iter_prefix(new_planned_era)
			.map(|(validator_stash, exposure)| {
				let mut exposure_clipped = exposure;
				let clipped_max_len = T::MaxNominatorRewardedPerValidator::get() as usize;
				if exposure_clipped.others.len() > clipped_max_len {
					exposure_clipped.others.sort_by(|a, b| a.value.cmp(&b.value).reverse());
					exposure_clipped.others.truncate(clipped_max_len);
				}
				<ErasStakersClipped<T>>::insert(
					&new_planned_era,
					&validator_stash,
					exposure_clipped,
				);

				validator_stash
			})
			.collect::<Vec<_>>();

		// then update all the prefs, only once per validator.
		for stash in &elected_stashes {
			let pref = Self::validators(stash);
			<ErasValidatorPrefs<T>>::insert(&new_planned_era, stash, pref);
		}

		log!(
			info,
			"finalizing staker info storage for era {}, {} validators have been elected",
			new_planned_era,
			elected_stashes.len()
		);

		elected_stashes
	}

	/// Consume a set of [`BoundedSupportsOf`] and collect them into set of [`Exposure`].
	///
	/// These exposures must represent validators in a single page, and comply with its
	/// corresponding bounds.
	pub(crate) fn collect_page_exposures(
		supports: BoundedSupportsOf<T::ElectionProvider>,
	) -> BoundedVec<(T::AccountId, Exposure<T>), MaxExposuresPerPageOf<T>> {
		let total_issuance = T::Currency::total_issuance();
		let to_currency = |e: ExtendedBalance| T::CurrencyToVote::to_currency(e, total_issuance);

		supports
			.into_iter()
			.map(|(validator, support)| {
				let mut others =
					BoundedVec::<_, MaxIndividualExposuresOf<T>>::with_bounded_capacity(
						support.voters.len(),
					);
				let mut own: BalanceOf<T> = Zero::zero();
				let mut total: BalanceOf<T> = Zero::zero();
				support
					.voters
					.into_iter()
					.map(|(nominator, weight)| (nominator, to_currency(weight)))
					.for_each(|(nominator, stake)| {
						if nominator == validator {
							debug_assert!(own.is_zero(), "own can only be set once");
							own = own.saturating_add(stake);
						} else {
							// defensive: ElectionProvider must guarantee that the aggregate number
							// of backers per validator does not exceed
							// ElectionProvider::MaxBackersPerWinner, which is the bound used in
							// `Exposure.others`. If this assumption is not held, this is a bug in
							// the election provider, not something that we can and should deal with
							// here. Here, we simply silently drop that winner.
							let _outcome = others
								.try_push(IndividualExposure { who: nominator, value: stake })
								.map_err(|_| {
									debug_assert!(false, "defensive error occurred.");
									log!(error, "defensive error occurred.");
								});
						}
						total = total.saturating_add(stake);
					});

				let exposure = Exposure { own, others, total };
				(validator, exposure)
			})
			.try_collect()
			.expect("`BoundedSupports` has the same bound as `MaxExposuresPerPageOf`; iterator chain does not alter length; qed")
	}

	/// Remove all associated data of a stash account from the staking system.
	///
	/// Assumes storage is upgraded before calling.
	///
	/// This is called:
	/// - after a `withdraw_unbonded()` call that frees all of a stash's bonded balance.
	/// - through `reap_stash()` if the balance has fallen to zero (through slashing).
	pub(crate) fn kill_stash(stash: &T::AccountId, num_slashing_spans: u32) -> DispatchResult {
		let controller = <Bonded<T>>::get(stash).ok_or(Error::<T>::NotStash)?;

		slashing::clear_stash_metadata::<T>(stash, num_slashing_spans)?;

		<Bonded<T>>::remove(stash);
		<Ledger<T>>::remove(&controller);

		<Payee<T>>::remove(stash);
		Self::do_remove_validator(stash);
		Self::do_remove_nominator(stash);

		frame_system::Pallet::<T>::dec_consumers(stash);

		Ok(())
	}

	/// Clear all era information for given era.
	pub(crate) fn clear_era_information(era_index: EraIndex) {
		<ErasStakers<T>>::remove_prefix(era_index, None);
		<ErasStakersClipped<T>>::remove_prefix(era_index, None);
		<ErasValidatorPrefs<T>>::remove_prefix(era_index, None);
		<ErasValidatorReward<T>>::remove(era_index);
		<ErasRewardPoints<T>>::remove(era_index);
		<ErasTotalStake<T>>::remove(era_index);
		ErasStartSessionIndex::<T>::remove(era_index);
	}

	/// Apply previously-unapplied slashes on the beginning of a new era, after a delay.
	fn apply_unapplied_slashes(active_era: EraIndex) {
		let slash_defer_duration = T::SlashDeferDuration::get();
		<Self as Store>::EarliestUnappliedSlash::mutate(|earliest| {
			if let Some(ref mut earliest) = earliest {
				let keep_from = active_era.saturating_sub(slash_defer_duration);
				for era in (*earliest)..keep_from {
					let era_slashes = <Self as Store>::UnappliedSlashes::take(&era);
					for slash in era_slashes {
						slashing::apply_slash::<T>(slash);
					}
				}

				*earliest = (*earliest).max(keep_from)
			}
		})
	}

	/// Add reward points to validators using their stash account ID.
	///
	/// Validators are keyed by stash account ID and must be in the current elected set.
	///
	/// For each element in the iterator the given number of points in u32 is added to the
	/// validator, thus duplicates are handled.
	///
	/// At the end of the era each the total payout will be distributed among validator
	/// relatively to their points.
	///
	/// COMPLEXITY: Complexity is `number_of_validator_to_reward x current_elected_len`.
	pub fn reward_by_ids(validators_points: impl IntoIterator<Item = (T::AccountId, u32)>) {
		if let Some(active_era) = Self::active_era() {
			<ErasRewardPoints<T>>::mutate(active_era.index, |era_rewards| {
				for (validator, points) in validators_points.into_iter() {
					*era_rewards.individual.entry(validator).or_default() += points;
					era_rewards.total += points;
				}
			});
		}
	}

	/// Ensures that at the end of the current session there will be a new era.
	pub(crate) fn ensure_new_era() {
		match ForceEra::<T>::get() {
			Forcing::ForceAlways | Forcing::ForceNew => (),
			_ => ForceEra::<T>::put(Forcing::ForceNew),
		}
	}

	#[cfg(feature = "runtime-benchmarks")]
	pub fn add_era_stakers(current_era: EraIndex, controller: T::AccountId, exposure: Exposure<T>) {
		<ErasStakers<T>>::insert(&current_era, &controller, &exposure);
	}

	#[cfg(feature = "runtime-benchmarks")]
	pub fn set_slash_reward_fraction(fraction: Perbill) {
		SlashRewardFraction::<T>::put(fraction);
	}

	/// Continue getting the npos voters.
	pub fn get_npos_voters_continue(
		maybe_max_len: Option<usize>,
		remaining: PageIndex,
		last: T::AccountId,
		slashing_spans: &BTreeMap<T::AccountId, slashing::SlashingSpans>,
	) -> Vec<(T::AccountId, VoteWeight, BoundedVec<T::AccountId, T::MaxNominations>)> {
		let to_take = maybe_max_len.unwrap_or(usize::MAX);

		let mut round_voters = vec![];
		for nominator in T::SortedListProvider::iter_from(&last).unwrap().take(to_take) {
			if let Some(Nominations { submitted_in, mut targets, suppressed: _ }) =
				<Nominators<T>>::get(&nominator)
			{
				targets.retain(|stash| {
					slashing_spans
						.get(stash)
						.map_or(true, |spans| submitted_in >= spans.last_nonzero_slash())
				});
				if !targets.len().is_zero() {
					round_voters.push((nominator.clone(), Self::weight_of(&nominator), targets));
				}
			} else {
				log!(error, "invalid item in `SortedListProvider`: {:?}", nominator)
			}
		}

		match remaining {
			0 => LastIteratedNominator::<T>::kill(),
			_ => {
				LastIteratedNominator::<T>::put(round_voters.last().map(|(x, _, _)| x).cloned());
			},
		};

		// TODO: register weight.

		round_voters
	}

	/// TODO:
	pub fn get_npos_voters_init(
		maybe_max_len: Option<usize>,
		remaining: PageIndex,
		slashing_spans: &BTreeMap<T::AccountId, slashing::SlashingSpans>,
	) -> Vec<VoterOf<Self>> {
		let max_allowed_len = {
			let nominator_count = Nominators::<T>::count() as usize;
			let validator_count = Validators::<T>::count() as usize;

			let all_voter_count = validator_count.saturating_add(nominator_count);
			maybe_max_len.unwrap_or(all_voter_count).min(all_voter_count)
		};

		let mut all_voters = Vec::<_>::with_capacity(max_allowed_len);

		// first, grab all validators, capped by the maximum allowed length.
		let mut validators_taken = 0u32;
		for (validator, _) in <Validators<T>>::iter().take(max_allowed_len) {
			// Append self vote.
			let self_vote = (
				validator.clone(),
				Self::weight_of(&validator),
				vec![validator.clone()]
					.try_into()
					.expect("`MaxVotesPerVoter` must be greater than or equal to 1"),
			);
			all_voters.push(self_vote);
			validators_taken.saturating_inc();
		}

		// .. and grab whatever we have left from nominators.
		let nominators_quota = (max_allowed_len as u32).saturating_sub(validators_taken);

		// track the count of nominators added to `all_voters
		let mut nominators_taken = 0u32;
		// track every nominator iterated over, but not necessarily added to `all_voters`
		let mut nominators_seen = 0u32;

		// cache the total-issuance once in this function
		let weight_of = Self::weight_of_fn();

		let mut nominators_iter = T::SortedListProvider::iter();
		while nominators_taken < nominators_quota && nominators_seen < nominators_quota * 2 {
			let nominator = match nominators_iter.next() {
				Some(nominator) => {
					nominators_seen.saturating_inc();
					nominator
				},
				None => break,
			};

			if let Some(Nominations { submitted_in, mut targets, suppressed: _ }) =
				<Nominators<T>>::get(&nominator)
			{
				targets.retain(|stash| {
					slashing_spans
						.get(stash)
						.map_or(true, |spans| submitted_in >= spans.last_nonzero_slash())
				});
				if !targets.len().is_zero() {
					if let Ok(bounded_targets) = targets.try_into() {
						all_voters.push((
							nominator.clone(),
							weight_of(&nominator),
							bounded_targets,
						));
						nominators_taken.saturating_inc();
					}
				}
			} else {
				// this can only happen if: 1. there a pretty bad bug in the bags-list (or whatever
				// is the sorted list) logic and the state of the two pallets is no longer
				// compatible, or because the nominators is not decodable since they have more
				// nomination than `T::MaxNominations`. This can rarely happen, and is not really an
				// emergency or bug if it does.
				log!(warn, "DEFENSIVE: invalid item in `SortedListProvider`: {:?}, this nominator probably has too many nominations now", nominator)
			}
		}

		match remaining {
			0 => LastIteratedNominator::<T>::kill(),
			_ => {
				LastIteratedNominator::<T>::put(all_voters.last().map(|(x, _, _)| x).cloned());
			},
		};

		// all_voters should have never re-allocated.
		debug_assert!(all_voters.capacity() >= all_voters.len());

		Self::register_weight(T::WeightInfo::get_npos_voters(
			validators_taken,
			nominators_taken,
			slashing_spans.len() as u32,
		));

		log!(
			debug,
			"generated {} npos voters, {} from validators and {} nominators, leftover calls: {}.",
			all_voters.len(),
			validators_taken,
			nominators_taken,
			remaining,
		);
		all_voters
	}

	/// Get the targets for an upcoming npos election.
	///
	/// This function is self-weighing as [`DispatchClass::Mandatory`].
	pub fn get_npos_targets() -> Vec<T::AccountId> {
		let mut validator_count = 0u32;
		let targets = Validators::<T>::iter()
			.map(|(v, _)| {
				validator_count.saturating_inc();
				v
			})
			.collect::<Vec<_>>();

		Self::register_weight(T::WeightInfo::get_npos_targets(validator_count));

		targets
	}

	/// This function will add a nominator to the `Nominators` storage map,
	/// and [`SortedListProvider`].
	///
	/// If the nominator already exists, their nominations will be updated.
	///
	/// NOTE: you must ALWAYS use this function to add nominator or update their targets. Any access
	/// to `Nominators` or `VoterList` outside of this function is almost certainly
	/// wrong.
	pub fn do_add_nominator(who: &T::AccountId, nominations: Nominations<T>) {
		if !Nominators::<T>::contains_key(who) {
			// maybe update sorted list. Error checking is defensive-only - this should never fail.
			let _ = T::SortedListProvider::on_insert(who.clone(), Self::weight_of(who))
				.defensive_unwrap_or_default();

			debug_assert_eq!(T::SortedListProvider::sanity_check(), Ok(()));
		}

		Nominators::<T>::insert(who, nominations);
	}

	/// This function will remove a nominator from the `Nominators` storage map,
	/// and [`SortedListProvider`].
	///
	/// Returns true if `who` was removed from `Nominators`, otherwise false.
	///
	/// NOTE: you must ALWAYS use this function to remove a nominator from the system. Any access to
	/// `Nominators` or `VoterList` outside of this function is almost certainly
	/// wrong.
	pub fn do_remove_nominator(who: &T::AccountId) -> bool {
		if Nominators::<T>::contains_key(who) {
			Nominators::<T>::remove(who);
			T::SortedListProvider::on_remove(who);
			debug_assert_eq!(T::SortedListProvider::sanity_check(), Ok(()));
			debug_assert_eq!(Nominators::<T>::count(), T::SortedListProvider::count());
			true
		} else {
			false
		}
	}

	/// This function will add a validator to the `Validators` storage map.
	///
	/// If the validator already exists, their preferences will be updated.
	///
	/// NOTE: you must ALWAYS use this function to add a validator to the system. Any access to
	/// `Validators` or `VoterList` outside of this function is almost certainly
	/// wrong.
	pub fn do_add_validator(who: &T::AccountId, prefs: ValidatorPrefs) {
		Validators::<T>::insert(who, prefs);
	}

	/// This function will remove a validator from the `Validators` storage map.
	///
	/// Returns true if `who` was removed from `Validators`, otherwise false.
	///
	/// NOTE: you must ALWAYS use this function to remove a validator from the system. Any access to
	/// `Validators` or `VoterList` outside of this function is almost certainly
	/// wrong.
	pub fn do_remove_validator(who: &T::AccountId) -> bool {
		if Validators::<T>::contains_key(who) {
			Validators::<T>::remove(who);
			true
		} else {
			false
		}
	}

	/// Register some amount of weight directly with the system pallet.
	///
	/// This is always mandatory weight.
	fn register_weight(weight: Weight) {
		<frame_system::Pallet<T>>::register_extra_weight_unchecked(
			weight,
			DispatchClass::Mandatory,
		);
	}
}

impl<T: Config> ElectionDataProvider for Pallet<T> {
	type AccountId = T::AccountId;
	type BlockNumber = BlockNumberFor<T>;
	type MaxVotesPerVoter = T::MaxNominations;

	fn desired_targets() -> data_provider::Result<u32> {
		Self::register_weight(T::DbWeight::get().reads(1));
		Ok(Self::validator_count())
	}

	fn electing_voters(
		maybe_max_len: Option<usize>,
		remaining: PageIndex,
	) -> data_provider::Result<Vec<VoterOf<Self>>> {
		let slashing_spans = <SlashingSpans<T>>::iter().collect::<BTreeMap<_, _>>();
		if let Some(last) = LastIteratedNominator::<T>::get() {
			Ok(Self::get_npos_voters_continue(maybe_max_len, remaining, last, &slashing_spans))
		} else {
			Ok(Self::get_npos_voters_init(maybe_max_len, remaining, &slashing_spans))
		}
	}

	fn electable_targets(
		maybe_max_len: Option<usize>,
		remaining: PageIndex,
	) -> data_provider::Result<Vec<T::AccountId>> {
		if remaining > Zero::zero() {
			return Err("Targets must only have page size 0.")
		}

		let target_count = Validators::<T>::count() as usize;

		// We can't handle this case yet -- return an error.
		if maybe_max_len.map_or(false, |max_len| target_count > max_len) {
			return Err("Target snapshot too big")
		}

		Ok(Self::get_npos_targets())
	}

	fn next_election_prediction(now: T::BlockNumber) -> T::BlockNumber {
		let current_era = Self::current_era().unwrap_or(0);
		let current_session = Self::current_planned_session();
		let current_era_start_session_index =
			Self::eras_start_session_index(current_era).unwrap_or(0);
		// Number of session in the current era or the maximum session per era if reached.
		let era_progress = current_session
			.saturating_sub(current_era_start_session_index)
			.min(T::SessionsPerEra::get());

		let until_this_session_end = T::NextNewSession::estimate_next_new_session(now)
			.0
			.unwrap_or_default()
			.saturating_sub(now);

		let session_length = T::NextNewSession::average_session_length();

		let sessions_left: T::BlockNumber = match ForceEra::<T>::get() {
			Forcing::ForceNone => Bounded::max_value(),
			Forcing::ForceNew | Forcing::ForceAlways => Zero::zero(),
			Forcing::NotForcing if era_progress >= T::SessionsPerEra::get() => Zero::zero(),
			Forcing::NotForcing => T::SessionsPerEra::get()
				.saturating_sub(era_progress)
				// One session is computed in this_session_end.
				.saturating_sub(1)
				.into(),
		};

		now.saturating_add(
			until_this_session_end.saturating_add(sessions_left.saturating_mul(session_length)),
		)
		.saturating_sub(T::ElectionProviderLookahead::get())
		.saturating_sub(PagesOf::<T>::get().into())
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn add_voter(
		voter: T::AccountId,
		weight: VoteWeight,
		targets: BoundedVec<T::AccountId, Self::MaxVotesPerVoter>,
	) {
		let stake = <BalanceOf<T>>::try_from(weight).unwrap_or_else(|_| {
			panic!("cannot convert a VoteWeight into BalanceOf, benchmark needs reconfiguring.")
		});
		<Bonded<T>>::insert(voter.clone(), voter.clone());
		<Ledger<T>>::insert(
			voter.clone(),
			StakingLedger {
				stash: voter.clone(),
				active: stake,
				total: stake,
				unlocking: Default::default(),
				claimed_rewards: vec![],
			},
		);

		Self::do_add_nominator(&voter, Nominations { targets, submitted_in: 0, suppressed: false });
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn add_target(target: T::AccountId) {
		let stake = MinValidatorBond::<T>::get() * 100u32.into();
		<Bonded<T>>::insert(target.clone(), target.clone());
		<Ledger<T>>::insert(
			target.clone(),
			StakingLedger {
				stash: target.clone(),
				active: stake,
				total: stake,
				unlocking: Default::default(),
				claimed_rewards: vec![],
			},
		);
		Self::do_add_validator(
			&target,
			ValidatorPrefs { commission: Perbill::zero(), blocked: false },
		);
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn clear() {
		<Bonded<T>>::remove_all(None);
		<Ledger<T>>::remove_all(None);
		<Validators<T>>::remove_all();
		<Nominators<T>>::remove_all();

		T::SortedListProvider::unsafe_clear();
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn put_snapshot(
		voters: Vec<VoterOf<Self>>,
		targets: Vec<T::AccountId>,
		target_stake: Option<VoteWeight>,
	) {
		targets.into_iter().for_each(|v| {
			let stake: BalanceOf<T> = target_stake
				.and_then(|w| <BalanceOf<T>>::try_from(w).ok())
				.unwrap_or_else(|| MinNominatorBond::<T>::get() * 100u32.into());
			<Bonded<T>>::insert(v.clone(), v.clone());
			<Ledger<T>>::insert(
				v.clone(),
				StakingLedger {
					stash: v.clone(),
					active: stake,
					total: stake,
					unlocking: Default::default(),
					claimed_rewards: vec![],
				},
			);
			Self::do_add_validator(
				&v,
				ValidatorPrefs { commission: Perbill::zero(), blocked: false },
			);
		});

		voters.into_iter().for_each(|(v, s, t)| {
			let stake = <BalanceOf<T>>::try_from(s).unwrap_or_else(|_| {
				panic!("cannot convert a VoteWeight into BalanceOf, benchmark needs reconfiguring.")
			});
			<Bonded<T>>::insert(v.clone(), v.clone());
			<Ledger<T>>::insert(
				v.clone(),
				StakingLedger {
					stash: v.clone(),
					active: stake,
					total: stake,
					unlocking: Default::default(),
					claimed_rewards: vec![],
				},
			);
			Self::do_add_nominator(
				&v,
				Nominations { targets: t.try_into().unwrap(), submitted_in: 0, suppressed: false },
			);
		});
	}
}

/// In this implementation `new_session(session)` must be called before `end_session(session-1)`
/// i.e. the new session must be planned before the ending of the previous session.
///
/// Once the first new_session is planned, all session must start and then end in order, though
/// some session can lag in between the newest session planned and the latest session started.
impl<T: Config> pallet_session::SessionManager<T::AccountId> for Pallet<T> {
	fn new_session(new_index: SessionIndex) -> Option<Vec<T::AccountId>> {
		log!(info, "planning new session {}", new_index);
		CurrentPlannedSession::<T>::put(new_index);
		Self::new_session(new_index, false)
	}
	fn new_session_genesis(new_index: SessionIndex) -> Option<Vec<T::AccountId>> {
		log!(info, "planning new session {} at genesis", new_index);
		CurrentPlannedSession::<T>::put(new_index);
		Self::new_session(new_index, true)
	}
	fn start_session(start_index: SessionIndex) {
		log!(info, "starting session {}", start_index);
		Self::start_session(start_index)
	}
	fn end_session(end_index: SessionIndex) {
		log!(info, "ending session {}", end_index);
		Self::end_session(end_index)
	}
}

impl<T: Config> historical::SessionManager<T::AccountId, Exposure<T>> for Pallet<T> {
	fn new_session(new_index: SessionIndex) -> Option<Vec<(T::AccountId, Exposure<T>)>> {
		<Self as pallet_session::SessionManager<_>>::new_session(new_index).map(|validators| {
			let current_era = Self::current_era()
				// Must be some as a new era has been created.
				.unwrap_or(0);

			validators
				.into_iter()
				.map(|v| {
					let exposure = Self::eras_stakers(current_era, &v);
					(v, exposure)
				})
				.collect()
		})
	}
	fn new_session_genesis(new_index: SessionIndex) -> Option<Vec<(T::AccountId, Exposure<T>)>> {
		<Self as pallet_session::SessionManager<_>>::new_session_genesis(new_index).map(
			|validators| {
				let current_era = Self::current_era()
					// Must be some as a new era has been created.
					.unwrap_or(0);

				validators
					.into_iter()
					.map(|v| {
						let exposure = Self::eras_stakers(current_era, &v);
						(v, exposure)
					})
					.collect()
			},
		)
	}
	fn start_session(start_index: SessionIndex) {
		<Self as pallet_session::SessionManager<_>>::start_session(start_index)
	}
	fn end_session(end_index: SessionIndex) {
		<Self as pallet_session::SessionManager<_>>::end_session(end_index)
	}
}

/// Add reward points to block authors:
/// * 20 points to the block producer for producing a (non-uncle) block in the relay chain,
/// * 2 points to the block producer for each reference to a previously unreferenced uncle, and
/// * 1 point to the producer of each referenced uncle block.
impl<T> pallet_authorship::EventHandler<T::AccountId, T::BlockNumber> for Pallet<T>
where
	T: Config + pallet_authorship::Config + pallet_session::Config,
{
	fn note_author(author: T::AccountId) {
		Self::reward_by_ids(vec![(author, 20)])
	}
	fn note_uncle(uncle_author: T::AccountId, _age: T::BlockNumber) {
		// defensive-only: block author must exist.
		if let Some(block_author) = <pallet_authorship::Pallet<T>>::author() {
			Self::reward_by_ids(vec![(block_author, 2), (uncle_author, 1)])
		} else {
			crate::log!(warn, "block author not set, this should never happen");
		}
	}
}

/// This is intended to be used with `FilterHistoricalOffences`.
impl<T: Config>
	OnOffenceHandler<T::AccountId, pallet_session::historical::IdentificationTuple<T>, Weight>
	for Pallet<T>
where
	T: pallet_session::Config<ValidatorId = <T as frame_system::Config>::AccountId>,
	T: pallet_session::historical::Config<
		FullIdentification = Exposure<T>,
		FullIdentificationOf = ExposureOf<T>,
	>,
	T::SessionHandler: pallet_session::SessionHandler<<T as frame_system::Config>::AccountId>,
	T::SessionManager: pallet_session::SessionManager<<T as frame_system::Config>::AccountId>,
	T::ValidatorIdOf: Convert<
		<T as frame_system::Config>::AccountId,
		Option<<T as frame_system::Config>::AccountId>,
	>,
{
	fn on_offence(
		offenders: &[OffenceDetails<
			T::AccountId,
			pallet_session::historical::IdentificationTuple<T>,
		>],
		slash_fraction: &[Perbill],
		slash_session: SessionIndex,
		disable_strategy: DisableStrategy,
	) -> Weight {
		let reward_proportion = SlashRewardFraction::<T>::get();
		let mut consumed_weight: Weight = 0;
		let mut add_db_reads_writes = |reads, writes| {
			consumed_weight += T::DbWeight::get().reads_writes(reads, writes);
		};

		let active_era = {
			let active_era = Self::active_era();
			add_db_reads_writes(1, 0);
			if active_era.is_none() {
				// This offence need not be re-submitted.
				return consumed_weight
			}
			active_era.expect("value checked not to be `None`; qed").index
		};
		let active_era_start_session_index = Self::eras_start_session_index(active_era)
			.unwrap_or_else(|| {
				frame_support::print("Error: start_session_index must be set for current_era");
				0
			});
		add_db_reads_writes(1, 0);

		let window_start = active_era.saturating_sub(T::BondingDuration::get());

		// Fast path for active-era report - most likely.
		// `slash_session` cannot be in a future active era. It must be in `active_era` or before.
		let slash_era = if slash_session >= active_era_start_session_index {
			active_era
		} else {
			let eras = BondedEras::<T>::get();
			add_db_reads_writes(1, 0);

			// Reverse because it's more likely to find reports from recent eras.
			match eras.iter().rev().find(|&&(_, ref sesh)| sesh <= &slash_session) {
				Some(&(ref slash_era, _)) => *slash_era,
				// Before bonding period. defensive - should be filtered out.
				None => return consumed_weight,
			}
		};

		<Self as Store>::EarliestUnappliedSlash::mutate(|earliest| {
			if earliest.is_none() {
				*earliest = Some(active_era)
			}
		});
		add_db_reads_writes(1, 1);

		let slash_defer_duration = T::SlashDeferDuration::get();

		let invulnerables = Self::invulnerables();
		add_db_reads_writes(1, 0);

		for (details, slash_fraction) in offenders.iter().zip(slash_fraction) {
			let (stash, exposure) = &details.offender;

			// Skip if the validator is invulnerable.
			if invulnerables.contains(stash) {
				continue
			}

			let unapplied = slashing::compute_slash::<T>(slashing::SlashParams {
				stash,
				slash: *slash_fraction,
				exposure,
				slash_era,
				window_start,
				now: active_era,
				reward_proportion,
				disable_strategy,
			});

			if let Some(mut unapplied) = unapplied {
				let nominators_len = unapplied.others.len() as u64;
				let reporters_len = details.reporters.len() as u64;

				{
					let upper_bound = 1 /* Validator/NominatorSlashInEra */ + 2 /* fetch_spans */;
					let rw = upper_bound + nominators_len * upper_bound;
					add_db_reads_writes(rw, rw);
				}
				unapplied.reporters = details.reporters.clone();
				if slash_defer_duration == 0 {
					// Apply right away.
					slashing::apply_slash::<T>(unapplied);
					{
						let slash_cost = (6, 5);
						let reward_cost = (2, 2);
						add_db_reads_writes(
							(1 + nominators_len) * slash_cost.0 + reward_cost.0 * reporters_len,
							(1 + nominators_len) * slash_cost.1 + reward_cost.1 * reporters_len,
						);
					}
				} else {
					// Defer to end of some `slash_defer_duration` from now.
					<Self as Store>::UnappliedSlashes::mutate(active_era, move |for_later| {
						for_later.push(unapplied)
					});
					add_db_reads_writes(1, 1);
				}
			} else {
				add_db_reads_writes(4 /* fetch_spans */, 5 /* kick_out_if_recent */)
			}
		}

		consumed_weight
	}
}

impl<T: Config> ScoreProvider<T::AccountId> for Pallet<T> {
	type Score = VoteWeight;

	fn score(who: &T::AccountId) -> Self::Score {
		Self::weight_of(who)
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn set_score_of(who: &T::AccountId, weight: Self::Score) {
		// this will clearly results in an inconsistent state, but it should not matter for a
		// benchmark.
		let active: BalanceOf<T> = weight.try_into().map_err(|_| ()).unwrap();
		let mut ledger = match Self::ledger(who) {
			None => StakingLedger::default_from(who.clone()),
			Some(l) => l,
		};
		ledger.active = active;

		<Ledger<T>>::insert(who, ledger);
		<Bonded<T>>::insert(who, who);

		// also, we play a trick to make sure that a issuance based-`CurrencyToVote` behaves well:
		// This will make sure that total issuance is zero, thus the currency to vote will be a 1-1
		// conversion.
		let imbalance = T::Currency::burn(T::Currency::total_issuance());
		// kinda ugly, but gets the job done. The fact that this works here is a HUGE exception.
		// Don't try this pattern in other places.
		sp_std::mem::forget(imbalance);
	}
}

/// A simple voter list implementation that does not require any additional pallets. Note, this
/// does not provided nominators in sorted ordered. If you desire nominators in a sorted order take
/// a look at [`pallet-bags-list].
pub struct UseNominatorsMap<T>(sp_std::marker::PhantomData<T>);
impl<T: Config> SortedListProvider<T::AccountId> for UseNominatorsMap<T> {
	type Error = ();
	type Score = VoteWeight;

	/// Returns iterator over voter list, which can have `take` called on it.
	fn iter() -> Box<dyn Iterator<Item = T::AccountId>> {
		Box::new(Nominators::<T>::iter().map(|(n, _)| n))
	}

	fn iter_from(
		start: &T::AccountId,
	) -> Result<Box<dyn Iterator<Item = T::AccountId>>, Self::Error> {
		if Nominators::<T>::contains_key(start) {
			let start_key = Nominators::<T>::hashed_key_for(start);
			Ok(Box::new(Nominators::<T>::iter_from(start_key).map(|(n, _)| n)))
		} else {
			Err(())
		}
	}

	fn count() -> u32 {
		Nominators::<T>::count()
	}

	fn contains(id: &T::AccountId) -> bool {
		Nominators::<T>::contains_key(id)
	}
	fn on_insert(_: T::AccountId, _: Self::Score) -> Result<(), Self::Error> {
		// nothing to do on insert.
		Ok(())
	}
	fn on_update(_: &T::AccountId, _: Self::Score) {
		// nothing to do on update.
	}

	fn on_remove(_: &T::AccountId) {
		// nothing to do on remove.
	}

	fn unsafe_regenerate(
		_: impl IntoIterator<Item = T::AccountId>,
		_: Box<dyn Fn(&T::AccountId) -> Self::Score>,
	) -> u32 {
		// nothing to do upon regenerate.
		0
	}

	fn sanity_check() -> Result<(), &'static str> {
		Ok(())
	}

	fn unsafe_clear() {
		// NOTE: Caller must ensure this doesn't lead to too many storage accesses. This is a
		// condition of SortedListProvider::unsafe_clear.
		Nominators::<T>::remove_all();
	}
}
