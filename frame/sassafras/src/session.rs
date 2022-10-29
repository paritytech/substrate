// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Sassafras implementation of traits required by session pallet.

use super::*;
use frame_support::traits::{EstimateNextSessionRotation, Hooks, OneSessionHandler};
use pallet_session::ShouldEndSession;
use sp_runtime::{traits::SaturatedConversion, Permill};

impl<T: Config> ShouldEndSession<T::BlockNumber> for Pallet<T> {
	fn should_end_session(now: T::BlockNumber) -> bool {
		// It might be (and it is in current implementation) that session module is calling
		// `should_end_session` from it's own `on_initialize` handler, in which case it's
		// possible that Sassafras's own `on_initialize` has not run yet, so let's ensure that we
		// have initialized the pallet and updated the current slot.
		Self::on_initialize(now);
		Self::should_end_epoch(now)
	}
}

impl<T: Config> OneSessionHandler<T::AccountId> for Pallet<T> {
	type Key = AuthorityId;

	fn on_genesis_session<'a, I: 'a>(validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, AuthorityId)>,
	{
		let authorities = validators.map(|(_, k)| (k, 1)).collect::<Vec<_>>();
		Self::initialize_genesis_authorities(&authorities);
	}

	fn on_new_session<'a, I: 'a>(_changed: bool, validators: I, queued_validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, AuthorityId)>,
	{
		let authorities = validators.map(|(_account, k)| (k, 1)).collect::<Vec<_>>();
		let bounded_authorities = WeakBoundedVec::<_, T::MaxAuthorities>::force_from(
			authorities,
			Some(
				"Warning: The session has more validators than expected. \
				A runtime configuration adjustment may be needed.",
			),
		);

		let next_authorities = queued_validators.map(|(_account, k)| (k, 1)).collect::<Vec<_>>();
		let next_bounded_authorities = WeakBoundedVec::<_, T::MaxAuthorities>::force_from(
			next_authorities,
			Some(
				"Warning: The session has more queued validators than expected. \
				A runtime configuration adjustment may be needed.",
			),
		);

		Self::enact_epoch_change(bounded_authorities, next_bounded_authorities)
	}

	fn on_disabled(i: u32) {
		Self::deposit_consensus(ConsensusLog::OnDisabled(i))
	}
}

impl<T: Config> EstimateNextSessionRotation<T::BlockNumber> for Pallet<T> {
	fn average_session_length() -> T::BlockNumber {
		T::EpochDuration::get().saturated_into()
	}

	fn estimate_current_session_progress(_now: T::BlockNumber) -> (Option<Permill>, Weight) {
		let elapsed = CurrentSlot::<T>::get().saturating_sub(Self::current_epoch_start()) + 1;
		let progress = Permill::from_rational(*elapsed, T::EpochDuration::get());

		// TODO-SASS-P2:  Read: Current Slot, Epoch Index, Genesis Slot
		(Some(progress), T::DbWeight::get().reads(3))
	}

	/// Return the _best guess_ block number, at which the next epoch change is predicted to happen.
	///
	/// Returns None if the prediction is in the past; This implies an internal error and should
	/// not happen under normal circumstances.
	///
	/// In other word, this is only accurate if no slots are missed. Given missed slots, the slot
	/// number will grow while the block number will not. Hence, the result can be interpreted as an
	/// upper bound.
	//
	// ## IMPORTANT NOTE
	//
	// This implementation is linked to how [`should_session_change`] is working. This might need
	// to be updated accordingly, if the underlying mechanics of slot and epochs change.
	fn estimate_next_session_rotation(now: T::BlockNumber) -> (Option<T::BlockNumber>, Weight) {
		let next_slot = Self::current_epoch_start().saturating_add(T::EpochDuration::get());
		let upper_bound = next_slot.checked_sub(*CurrentSlot::<T>::get()).map(|slots_remaining| {
			// This is a best effort guess. Drifts in the slot/block ratio will cause errors here.
			let blocks_remaining: T::BlockNumber = slots_remaining.saturated_into();
			now.saturating_add(blocks_remaining)
		});

		// TODO-SASS-P2:  Read: Current Slot, Epoch Index, Genesis Slot
		(upper_bound, T::DbWeight::get().reads(3))
	}
}
