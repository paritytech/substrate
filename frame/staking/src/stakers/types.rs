use super::*;
use codec::{Decode, Encode, HasCompact};
use frame_support::{
	traits::Currency, BoundedVec, EqNoBound, PartialEqNoBound, RuntimeDebugNoBound,
};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{AtLeast32BitUnsigned, Saturating, Zero},
	RuntimeDebug,
};
use sp_staking::EraIndex;

pub type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

/// Preference of what happens regarding validation.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, TypeInfo, Default, MaxEncodedLen)]
pub struct ValidatorPrefs {
	/// Reward that validator takes up-front; only the rest is split between themselves and
	/// nominators.
	#[codec(compact)]
	pub commission: Perbill,
	/// Whether or not this validator is accepting more nominations. If `true`, then no nominator
	/// who is not already nominating this validator may nominate them. By default, validators
	/// are accepting nominations.
	pub blocked: bool,
}

/// Just a Balance/BlockNumber tuple to encode when a chunk of funds will be unlocked.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct UnlockChunk<Balance: HasCompact> {
	/// Amount of funds to be unlocked.
	#[codec(compact)]
	pub(crate) value: Balance,
	/// Era number at which point it'll be unlocked.
	#[codec(compact)]
	pub(crate) era: EraIndex,
}

/// A record of the nominations made by a specific account.
#[derive(
	PartialEqNoBound, EqNoBound, Clone, Encode, Decode, RuntimeDebugNoBound, TypeInfo, MaxEncodedLen,
)]
#[codec(mel_bound())]
#[scale_info(skip_type_params(T))]
pub struct Nominations<T: super::Config> {
	/// The targets of nomination.
	pub targets: BoundedVec<T::AccountId, T::MaxNominations>,
	/// The era the nominations were submitted.
	///
	/// Except for initial nominations which are considered submitted at era 0.
	pub submitted_in: EraIndex,
	/// Whether the nominations have been suppressed. This can happen due to slashing of the
	/// validators, or other events that might invalidate the nomination.
	///
	/// NOTE: this for future proofing and is thus far not used.
	pub suppressed: bool,
}

/// Indicates the initial status of the staker.
#[derive(RuntimeDebug, TypeInfo)]
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize, Clone))]
pub enum StakerStatus<AccountId> {
	/// Chilling.
	Idle,
	/// Declared desire in validating or already participating in it.
	Validator,
	/// Nominating for a group of other stakers.
	Nominator(Vec<AccountId>),
}

/// The ledger of a (bonded) stash.
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
#[codec(mel_bound())]
#[scale_info(skip_type_params(T))]
pub struct StakingLedger<T: super::Config> {
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
}

impl<T: super::Config> StakingLedger<T>
where
	BalanceOf<T>: HasCompact + Copy + Saturating + AtLeast32BitUnsigned + Zero,
{
	/// Initializes the default object using the given `validator`.
	pub(super) fn default_from(stash: T::AccountId) -> Self {
		Self { stash, total: Zero::zero(), active: Zero::zero(), unlocking: Default::default() }
	}

	/// Remove entries from `unlocking` that are sufficiently old and reduce the
	/// total by the sum of their balances.
	pub(super) fn consolidate_unlocked(self, current_era: EraIndex) -> Self {
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

		Self { stash: self.stash, total, active: self.active, unlocking }
	}

	/// Re-bond funds that were scheduled for unlocking.
	///
	/// Returns the updated ledger, and the amount actually rebonded.
	pub(super) fn rebond(mut self, value: BalanceOf<T>) -> (Self, BalanceOf<T>) {
		let mut unlocking_balance: BalanceOf<T> = Zero::zero();

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
}

impl<T: super::Config> StakingLedger<T>
where
	BalanceOf<T>: AtLeast32BitUnsigned + Saturating + Copy,
{
	/// Slash the validator for a given amount of balance. This can grow the value
	/// of the slash in the case that the validator has less than `minimum_balance`
	/// active funds. Returns the amount of funds actually slashed.
	///
	/// Slashes from `active` funds first, and then `unlocking`, starting with the
	/// chunks that are closest to unlocking.
	fn slash(&mut self, mut value: BalanceOf<T>, minimum_balance: BalanceOf<T>) -> BalanceOf<T> {
		let pre_total = self.total;
		let total = &mut self.total;
		let active = &mut self.active;

		let slash_out_of = |total_remaining: &mut BalanceOf<T>,
		                    target: &mut BalanceOf<T>,
		                    value: &mut BalanceOf<T>| {
			let mut slash_from_target = (*value).min(*target);

			if !slash_from_target.is_zero() {
				*target -= slash_from_target;

				// Don't leave a dust balance in the staking system.
				if *target <= minimum_balance {
					slash_from_target += *target;
					*value += sp_std::mem::replace(target, Zero::zero());
				}

				*total_remaining = total_remaining.saturating_sub(slash_from_target);
				*value -= slash_from_target;
			}
		};

		slash_out_of(total, active, &mut value);

		let i = self
			.unlocking
			.iter_mut()
			.map(|chunk| {
				slash_out_of(total, &mut chunk.value, &mut value);
				chunk.value
			})
			.take_while(|value| value.is_zero()) // Take all fully-consumed chunks out.
			.count();

		// Kill all drained chunks.
		let _ = self.unlocking.drain(..i);

		pre_total.saturating_sub(*total)
	}
}
