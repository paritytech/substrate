// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Consensus extension module for Aura consensus. This manages offline reporting.

#![cfg_attr(not(feature = "std"), no_std)]

#[allow(unused_imports)]
#[macro_use]
extern crate sr_std as rstd;

#[macro_use]
extern crate srml_support as runtime_support;

extern crate sr_primitives as primitives;
extern crate srml_system as system;
extern crate srml_consensus as consensus;
extern crate srml_timestamp as timestamp;
extern crate srml_staking as staking;
extern crate substrate_primitives;

#[cfg(test)]
extern crate sr_io as runtime_io;

use rstd::prelude::*;
use runtime_support::storage::StorageValue;
use runtime_support::dispatch::Result;
use primitives::traits::{As, Zero};
use timestamp::OnTimestampSet;

mod mock;
mod tests;

pub trait Trait: consensus::Trait + timestamp::Trait { }

decl_storage! {
	trait Store for Module<T: Trait> as Aura {
		// The last timestamp.
		LastTimestamp get(last) build(|_| T::Moment::sa(0)): T::Moment;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin { }
}

/// A report of skipped authorities in aura.
pub struct AuraReport {
	// The first skipped authority.
	start_idx: usize,
	// The number of times authorities were skipped.
	skipped: usize,
}

impl AuraReport {
	/// Call the closure with (validator_indices, punishment_count) for each
	/// validator to punish.
	pub fn punish<F>(&self, validator_count: usize, punish_with: F)
		where F: Fn(usize, usize)
	{
		let start_idx = self.start_idx % validator_count;

		// the number of times everyone was skipped.
		let skipped_all = self.skipped / validator_count;
		// the number of validators who were skipped once after that.
		let skipped_after = self.skipped % validator_count;

		for i in (start_idx..).into_iter().chain(0..start_idx) {
			let slash_count = skipped_all + if i < skipped_after {
				1
			} else {
				// avoid iterating over all authorities when skipping a couple.
				if skipped_all == 0 { break }
				0
			};

			if slash_count > 0 {
				punish_with(i, slash_count);
			}
		}
	}
}

impl<T: Trait> Module<T>
	where T::OnOfflineValidator: consensus::OnOfflineValidator<AuraReport>,
{
	/// Determine the Aura slot-duration based on the timestamp module configuration.
	pub fn slot_duration() -> u64 {
		// we double the minimum block-period so each author can always propose within
		// the majority of their slot.
		<timestamp::Module<T>>::block_period().as_().saturating_mul(2)
	}

	/// Verify an inherent slot that is used in a block seal against a timestamp
	/// extracted from the block.
	// TODO: ensure `ProvideInherent` can deal with dependencies like this.
	pub fn verify_inherent(timestamp: T::Moment, seal_slot: u64) -> Result {
		let timestamp_based_slot = timestamp.as_() / Self::slot_duration();

		if timestamp_based_slot == seal_slot {
			Ok(())
		} else {
			Err("timestamp set in block doesn't match slot in seal".into())
		}
	}

	fn on_timestamp_set(now: T::Moment, slot_duration: T::Moment) {
		let last = Self::last();
		<Self as Store>::LastTimestamp::put(now.clone());

		if last == T::Moment::zero() {
			return;
		}

		assert!(slot_duration > T::Moment::zero(), "Aura slot duration cannot be zero.");

		let last_slot = last / slot_duration.clone();
		let first_skipped = last_slot.clone() + T::Moment::sa(1);
		let cur_slot = now / slot_duration;

		assert!(last_slot < cur_slot, "Only one block may be authored per slot.");
		if cur_slot == first_skipped { return }

		let slot_to_usize = |slot: T::Moment| { slot.as_() as usize };

		let skipped_slots = cur_slot - last_slot - T::Moment::sa(1);

		<T::OnOfflineValidator as consensus::OnOfflineValidator<_>>::on_offline_validator(AuraReport {
			start_idx: slot_to_usize(first_skipped),
			skipped: slot_to_usize(skipped_slots),
		})
	}
}

impl<T: Trait> OnTimestampSet<T::Moment> for Module<T>
	where T::OnOfflineValidator: consensus::OnOfflineValidator<AuraReport>,
{
	fn on_timestamp_set(moment: T::Moment) {
		Self::on_timestamp_set(moment, T::Moment::sa(Self::slot_duration()))
	}
}

/// A type for performing slashing based on aura reports.
pub struct StakingSlasher<T>(::rstd::marker::PhantomData<T>);

impl<T: staking::Trait + Trait> consensus::OnOfflineValidator<AuraReport> for StakingSlasher<T> {
	fn on_offline_validator(report: AuraReport) {
		let validators = staking::Module::<T>::validators();

		report.punish(
			validators.len(),
			|idx, slash_count| {
				let v = validators[idx].clone();
				staking::Module::<T>::on_offline_validator(v, slash_count);
			}
		);
	}
}
