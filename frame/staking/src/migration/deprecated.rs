// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

/// Deprecated storages used for migration from v1.0.0 to v2.0.0 only.

use crate::{Trait, BalanceOf, SessionIndex, Exposure, UnlockChunk, EraIndex};
use codec::{Encode, Decode, HasCompact};
use frame_support::{decl_module, decl_storage, traits::Time};
use sp_std::prelude::*;

pub type MomentOf<T> = <<T as Trait>::DeprecatedTime as Time>::Moment;

/// Information regarding the active era (era in used in session).
#[derive(Encode, Decode)]
pub struct ActiveEraInfo<Moment> {
	/// Index of era.
	pub index: EraIndex,
	/// Moment of start
	///
	/// Start can be none if start hasn't been set for the era yet,
	/// Start is set on the first on_finalize of the era to guarantee usage of `Time`.
	pub start: Option<Moment>,
}

/// Reward points of an era. Used to split era total payout between validators.
#[derive(Encode, Decode, Default)]
pub struct EraPoints {
	/// Total number of points. Equals the sum of reward points for each validator.
	pub total: u32,
	/// The reward points earned by a given validator. The index of this vec corresponds to the
	/// index into the current validator set.
	pub individual: Vec<u32>,
}

#[derive(Encode, Decode)]
pub struct OldStakingLedger<AccountId, Balance: HasCompact> {
	pub stash: AccountId,
	#[codec(compact)]
	pub total: Balance,
	#[codec(compact)]
	pub active: Balance,
	pub unlocking: Vec<UnlockChunk<Balance>>,
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
		pub CurrentEraStart: MomentOf<T>;

		/// The session index at which the current era started.
		pub CurrentEraStartSessionIndex: SessionIndex;

		/// Rewards for the current era. Using indices of current elected set.
		pub CurrentEraPointsEarned: EraPoints;

		/// Nominators for a particular account that is in action right now. You can't iterate
		/// through validators here, but you can find them in the Session module.
		///
		/// This is keyed by the stash account.
		pub Stakers: map hasher(blake2_256) T::AccountId => Exposure<T::AccountId, BalanceOf<T>>;

		/// Old upgrade flag.
		pub IsUpgraded: bool;

		/// Old active era information.
		///
		/// The active era information, it holds index and start.
		///
		/// The active era is the era currently rewarded.
		/// Validator set of this era must be equal to `SessionInterface::validators`.
		pub ActiveEra get(fn active_era): Option<ActiveEraInfo<MomentOf<T>>>;
	}
}
