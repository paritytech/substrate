use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	traits::{Defensive, Get, LockableCurrency, WithdrawReasons},
	BoundedVec, CloneNoBound, EqNoBound, PartialEqNoBound, RuntimeDebugNoBound,
};
use scale_info::TypeInfo;
use sp_runtime::{traits::Zero, Perquintill, Rounding, Saturating};
use sp_staking::{EraIndex, OnStakingUpdate, StakingAccount};
use sp_std::{collections::btree_map::BTreeMap, prelude::*};

use crate::{log, BalanceOf, Bonded, Config, Error, Ledger, UnlockChunk, STAKING_ID};

/// The ledger of a (bonded) stash.
///
/// Note: All the reads and mutations to the `Ledger` and `Bonded` storage items *MUST* be performed
/// through the methods exposed by this struct to ensure data and staking lock consistency.
#[derive(
	PartialEqNoBound,
	EqNoBound,
	CloneNoBound,
	Encode,
	Decode,
	RuntimeDebugNoBound,
	TypeInfo,
	MaxEncodedLen,
)]
#[scale_info(skip_type_params(T))]
pub struct StakingLedger<T: Config> {
	/// The stash account whose balance is actually locked and at stake.
	pub stash: T::AccountId,
	/// The total amount of the stash's balance that we are currently accounting for.
	/// It's just `active` plus all the `unlocking` balances.
	#[codec(compact)]
	pub total: BalanceOf<T>,
	/// The total amount of the stash's balance that will be at stake in any forthcoming
	/// rounds.
	#[codec(compact)]
	pub active: BalanceOf<T>,
	/// Any balance that is becoming free, which may eventually be transferred out of the stash
	/// (assuming it doesn't get slashed first). It is assumed that this will be treated as a first
	/// in, first out queue where the new (higher value) eras get pushed on the back.
	pub unlocking: BoundedVec<UnlockChunk<BalanceOf<T>>, T::MaxUnlockingChunks>,
	/// List of eras for which the stakers behind a validator have claimed rewards. Only updated
	/// for validators.
	pub claimed_rewards: BoundedVec<EraIndex, T::HistoryDepth>,
	/// The controller associated with this ledger's stash.
	///
	/// This is not stored on-chain, and is only bundled when the ledger is read from storage.
	/// Use [`controller`] function to get the controller associated with the ledger.
	#[codec(skip)]
	controller: Option<T::AccountId>,
}

impl<T: Config> StakingLedger<T> {
	#[cfg(any(feature = "runtime-benchmarks", test))]
	pub fn default_from(stash: T::AccountId) -> Self {
		Self {
			stash,
			total: Zero::zero(),
			active: Zero::zero(),
			unlocking: Default::default(),
			claimed_rewards: Default::default(),
			controller: Default::default(),
		}
	}

	/// Returns a new instance of a staking ledger.
	///
	/// The `Ledger` storage is not mutated. In order to store, `fn update` must be called on
	/// the returned staking ledger.
	///
	/// Note: as the controller accounts are being deprecated, the stash account is the same as the
	/// controller account.
	pub fn new(
		stash: T::AccountId,
		active_stake: BalanceOf<T>,
		total_stake: BalanceOf<T>,
		unlocking: BoundedVec<UnlockChunk<BalanceOf<T>>, T::MaxUnlockingChunks>,
		claimed_rewards: BoundedVec<EraIndex, T::HistoryDepth>,
	) -> Self {
		Self {
			stash: stash.clone(),
			active: active_stake,
			total: total_stake,
			unlocking,
			claimed_rewards,
			// controllers are deprecated and map 1-1 to stashes.
			controller: Some(stash),
		}
	}

	/// Returns the paired account, if any.
	///
	/// A "pair" refers to the tuple (stash, controller). If the input is a
	/// [`StakingAccount::Stash`] variant, its pair account will be of type
	/// [`StakingAccount::Controller`] and vice-versa.
	///
	/// This method is meant to abstract from the runtime development the difference between stash
	/// and controller. This will be deprecated once the controller is fully deprecated as well.
	pub(crate) fn paired_account(account: StakingAccount<T::AccountId>) -> Option<T::AccountId> {
		match account {
			StakingAccount::Stash(stash) => <Bonded<T>>::get(stash),
			StakingAccount::Controller(controller) =>
				<Ledger<T>>::get(&controller).map(|ledger| ledger.stash),
		}
	}

	/// Returns whether a given account is bonded.
	pub(crate) fn is_bonded(account: StakingAccount<T::AccountId>) -> bool {
		match account {
			StakingAccount::Stash(stash) => <Bonded<T>>::contains_key(stash),
			StakingAccount::Controller(controller) => <Ledger<T>>::contains_key(controller),
		}
	}

	/// Returns a staking ledger, if it is bonded and it exists in storage.
	///
	/// This getter can be called with either a controller or stash account, provided that the
	/// account is properly wrapped in the respective [`StakingAccount`] variant. This is meant to
	/// abstract the concept of controller/stash accounts to the caller.
	pub(crate) fn get(account: StakingAccount<T::AccountId>) -> Result<StakingLedger<T>, Error<T>> {
		let controller = match account {
			StakingAccount::Stash(stash) => <Bonded<T>>::get(stash).ok_or(Error::<T>::NotStash),
			StakingAccount::Controller(controller) => Ok(controller),
		}?;

		<Ledger<T>>::get(&controller)
			.map(|mut ledger| {
				ledger.controller = Some(controller.clone());
				ledger
			})
			.ok_or_else(|| Error::<T>::NotController)
	}

	/// Returns the controller account of a staking ledger.
	///
	/// Note: it will fallback into querying the `Bonded` storage with the ledger stash if the
	/// controller is not set in `self`, which most likely means that self was fetched directly from
	/// `Ledger` instead of through the methods exposed in `StakingLedger`. If the ledger does not
	/// exist in storage, it returns `None`.
	pub(crate) fn controller(&self) -> Option<T::AccountId> {
		self.controller
			.clone()
			.or_else(|| Self::paired_account(StakingAccount::Stash(self.stash.clone())))
	}

	/// Inserts/updates a staking ledger account.
	///
	/// Bonds the ledger if it is not bonded yet, signalling that this is a new ledger. The staking
	/// locks of the stash account are updated accordingly.
	///
	/// Note: To ensure lock consistency, all the [`Ledger`] storage updates should be made through
	/// this helper function.
	pub(crate) fn update(&self) -> Result<(), Error<T>> {
		if !<Bonded<T>>::contains_key(&self.stash) {
			// not bonded yet, new ledger. Note: controllers are deprecated, stash is the
			// controller.
			<Bonded<T>>::insert(&self.stash, &self.stash);
		}

		T::Currency::set_lock(STAKING_ID, &self.stash, self.total, WithdrawReasons::all());
		Ledger::<T>::insert(&self.controller().ok_or(Error::<T>::NotController)?, &self);

		Ok(())
	}

	// Bonds a ledger.
	//
	// This method is just syntactic sugar of [`Self::update`] with a check that returns an error if
	// the ledger has is already bonded to ensure that the method behaves as expected.
	pub(crate) fn bond(&self) -> Result<(), Error<T>> {
		if <Bonded<T>>::contains_key(&self.stash) {
			Err(Error::<T>::AlreadyBonded)
		} else {
			self.update()
		}
	}

	/// Clears all data related to a staking ledger and its bond in both [`Ledger`] and [`Bonded`]
	/// storage items and updates the stash staking lock.
	pub(crate) fn kill(stash: &T::AccountId) -> Result<(), Error<T>> {
		let controller = <Bonded<T>>::get(stash).ok_or(Error::<T>::NotStash)?;

		<Ledger<T>>::get(&controller).ok_or(Error::<T>::NotController).map(|ledger| {
			T::Currency::remove_lock(STAKING_ID, &ledger.stash);
			Ledger::<T>::remove(controller);

			Ok(())
		})?
	}

	/// Remove entries from `unlocking` that are sufficiently old and reduce the
	/// total by the sum of their balances.
	pub(crate) fn consolidate_unlocked(self, current_era: EraIndex) -> Self {
		let mut total = self.total;
		let unlocking: BoundedVec<_, _> = self
			.unlocking
			.into_iter()
			.filter(|chunk| {
				if chunk.era > current_era {
					true
				} else {
					total = total.saturating_sub(chunk.value);
					false
				}
			})
			.collect::<Vec<_>>()
			.try_into()
			.expect(
				"filtering items from a bounded vec always leaves length less than bounds. qed",
			);

		Self {
			stash: self.stash,
			total,
			active: self.active,
			unlocking,
			claimed_rewards: self.claimed_rewards,
			controller: self.controller,
		}
	}

	/// Re-bond funds that were scheduled for unlocking.
	///
	/// Returns the updated ledger, and the amount actually rebonded.
	pub(crate) fn rebond(mut self, value: BalanceOf<T>) -> (Self, BalanceOf<T>) {
		let mut unlocking_balance = BalanceOf::<T>::zero();

		while let Some(last) = self.unlocking.last_mut() {
			if unlocking_balance + last.value <= value {
				unlocking_balance += last.value;
				self.active += last.value;
				self.unlocking.pop();
			} else {
				let diff = value - unlocking_balance;

				unlocking_balance += diff;
				self.active += diff;
				last.value -= diff;
			}

			if unlocking_balance >= value {
				break
			}
		}

		(self, unlocking_balance)
	}

	/// Slash the staker for a given amount of balance.
	///
	/// This implements a proportional slashing system, whereby we set our preference to slash as
	/// such:
	///
	/// - If any unlocking chunks exist that are scheduled to be unlocked at `slash_era +
	///   bonding_duration` and onwards, the slash is divided equally between the active ledger and
	///   the unlocking chunks.
	/// - If no such chunks exist, then only the active balance is slashed.
	///
	/// Note that the above is only a *preference*. If for any reason the active ledger, with or
	/// without some portion of the unlocking chunks that are more justified to be slashed are not
	/// enough, then the slashing will continue and will consume as much of the active and unlocking
	/// chunks as needed.
	///
	/// This will never slash more than the given amount. If any of the chunks become dusted, the
	/// last chunk is slashed slightly less to compensate. Returns the amount of funds actually
	/// slashed.
	///
	/// `slash_era` is the era in which the slash (which is being enacted now) actually happened.
	///
	/// This calls `Config::OnStakingUpdate::on_slash` with information as to how the slash was
	/// applied.
	pub(crate) fn slash(
		&mut self,
		slash_amount: BalanceOf<T>,
		minimum_balance: BalanceOf<T>,
		slash_era: EraIndex,
	) -> BalanceOf<T> {
		if slash_amount.is_zero() {
			return Zero::zero()
		}

		use sp_runtime::PerThing as _;
		let mut remaining_slash = slash_amount;
		let pre_slash_total = self.total;

		// for a `slash_era = x`, any chunk that is scheduled to be unlocked at era `x + 28`
		// (assuming 28 is the bonding duration) onwards should be slashed.
		let slashable_chunks_start = slash_era + T::BondingDuration::get();

		// `Some(ratio)` if this is proportional, with `ratio`, `None` otherwise. In both cases, we
		// slash first the active chunk, and then `slash_chunks_priority`.
		let (maybe_proportional, slash_chunks_priority) = {
			if let Some(first_slashable_index) =
				self.unlocking.iter().position(|c| c.era >= slashable_chunks_start)
			{
				// If there exists a chunk who's after the first_slashable_start, then this is a
				// proportional slash, because we want to slash active and these chunks
				// proportionally.

				// The indices of the first chunk after the slash up through the most recent chunk.
				// (The most recent chunk is at greatest from this era)
				let affected_indices = first_slashable_index..self.unlocking.len();
				let unbonding_affected_balance =
					affected_indices.clone().fold(BalanceOf::<T>::zero(), |sum, i| {
						if let Some(chunk) = self.unlocking.get(i).defensive() {
							sum.saturating_add(chunk.value)
						} else {
							sum
						}
					});
				let affected_balance = self.active.saturating_add(unbonding_affected_balance);
				let ratio = Perquintill::from_rational_with_rounding(
					slash_amount,
					affected_balance,
					Rounding::Up,
				)
				.unwrap_or_else(|_| Perquintill::one());
				(
					Some(ratio),
					affected_indices.chain((0..first_slashable_index).rev()).collect::<Vec<_>>(),
				)
			} else {
				// We just slash from the last chunk to the most recent one, if need be.
				(None, (0..self.unlocking.len()).rev().collect::<Vec<_>>())
			}
		};

		// Helper to update `target` and the ledgers total after accounting for slashing `target`.
		log!(
			debug,
			"slashing {:?} for era {:?} out of {:?}, priority: {:?}, proportional = {:?}",
			slash_amount,
			slash_era,
			self,
			slash_chunks_priority,
			maybe_proportional,
		);

		let mut slash_out_of = |target: &mut BalanceOf<T>, slash_remaining: &mut BalanceOf<T>| {
			let mut slash_from_target = if let Some(ratio) = maybe_proportional {
				ratio.mul_ceil(*target)
			} else {
				*slash_remaining
			}
			// this is the total that that the slash target has. We can't slash more than
			// this anyhow!
			.min(*target)
			// this is the total amount that we would have wanted to slash
			// non-proportionally, a proportional slash should never exceed this either!
			.min(*slash_remaining);

			// slash out from *target exactly `slash_from_target`.
			*target = *target - slash_from_target;
			if *target < minimum_balance {
				// Slash the rest of the target if it's dust. This might cause the last chunk to be
				// slightly under-slashed, by at most `MaxUnlockingChunks * ED`, which is not a big
				// deal.
				slash_from_target =
					sp_std::mem::replace(target, Zero::zero()).saturating_add(slash_from_target)
			}

			self.total = self.total.saturating_sub(slash_from_target);
			*slash_remaining = slash_remaining.saturating_sub(slash_from_target);
		};

		// If this is *not* a proportional slash, the active will always wiped to 0.
		slash_out_of(&mut self.active, &mut remaining_slash);

		let mut slashed_unlocking = BTreeMap::<_, _>::new();
		for i in slash_chunks_priority {
			if remaining_slash.is_zero() {
				break
			}

			if let Some(chunk) = self.unlocking.get_mut(i).defensive() {
				slash_out_of(&mut chunk.value, &mut remaining_slash);
				// write the new slashed value of this chunk to the map.
				slashed_unlocking.insert(chunk.era, chunk.value);
			} else {
				break
			}
		}

		// clean unlocking chunks that are set to zero.
		self.unlocking.retain(|c| !c.value.is_zero());

		T::EventListeners::on_slash(&self.stash, self.active, &slashed_unlocking);
		pre_slash_total.saturating_sub(self.total)
	}
}

// This structs makes it easy to write tests to compare staking ledgers fetched from storage. This
// is required because the controller field is not stored in storage and it is private.
#[cfg(test)]
#[derive(frame_support::DebugNoBound, Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub struct StakingLedgerInspect<T: Config> {
	pub stash: T::AccountId,
	#[codec(compact)]
	pub total: BalanceOf<T>,
	#[codec(compact)]
	pub active: BalanceOf<T>,
	pub unlocking: BoundedVec<UnlockChunk<BalanceOf<T>>, T::MaxUnlockingChunks>,
	pub claimed_rewards: BoundedVec<EraIndex, T::HistoryDepth>,
}

#[cfg(test)]
impl<T: Config> PartialEq<StakingLedgerInspect<T>> for StakingLedger<T> {
	fn eq(&self, other: &StakingLedgerInspect<T>) -> bool {
		self.stash == other.stash &&
			self.total == other.total &&
			self.active == other.active &&
			self.unlocking == other.unlocking &&
			self.claimed_rewards == other.claimed_rewards
	}
}

#[cfg(test)]
impl<T: Config> codec::EncodeLike<StakingLedger<T>> for StakingLedgerInspect<T> {}
