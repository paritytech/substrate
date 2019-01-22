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

extern crate sr_std as rstd;

#[macro_use]
extern crate parity_codec_derive;
extern crate parity_codec;

#[macro_use]
extern crate srml_support as runtime_support;

extern crate sr_primitives as primitives;
extern crate srml_system as system;
pub extern crate srml_timestamp as timestamp;
extern crate srml_staking as staking;
extern crate substrate_primitives;
extern crate substrate_inherents as inherents;

#[cfg(test)]
extern crate srml_consensus as consensus;

#[cfg(test)]
extern crate sr_io as runtime_io;

#[cfg(test)]
#[macro_use]
extern crate lazy_static;

#[cfg(test)]
extern crate parking_lot;

use rstd::{result, prelude::*};
use runtime_support::storage::StorageValue;
use primitives::traits::{As, Zero};
use timestamp::OnTimestampSet;
#[cfg(feature = "std")]
use timestamp::TimestampInherentData;
#[cfg(feature = "std")]
use parity_codec::Decode;
use inherents::{RuntimeString, InherentIdentifier, InherentData, ProvideInherent, MakeFatalError};
#[cfg(feature = "std")]
use inherents::{InherentDataProviders, ProvideInherentData};

mod mock;
mod tests;

/// The aura inherent identifier.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"auraslot";

/// The type of the aura inherent.
pub type InherentType = u64;

/// Auxiliary trait to extract aura inherent data.
pub trait AuraInherentData {
	/// Get aura inherent data.
	fn aura_inherent_data(&self) -> result::Result<InherentType, RuntimeString>;
	/// Replace aura inherent data.
	fn aura_replace_inherent_data(&mut self, new: InherentType);
}

impl AuraInherentData for InherentData {
	fn aura_inherent_data(&self) -> result::Result<InherentType, RuntimeString> {
		self.get_data(&INHERENT_IDENTIFIER)
			.and_then(|r| r.ok_or_else(|| "Aura inherent data not found".into()))
	}

	fn aura_replace_inherent_data(&mut self, new: InherentType) {
		self.replace_data(INHERENT_IDENTIFIER, &new);
	}
}

/// Provides the slot duration inherent data for `Aura`.
#[cfg(feature = "std")]
pub struct InherentDataProvider {
	slot_duration: u64,
}

#[cfg(feature = "std")]
impl InherentDataProvider {
	pub fn new(slot_duration: u64) -> Self {
		Self {
			slot_duration
		}
	}
}

#[cfg(feature = "std")]
impl ProvideInherentData for InherentDataProvider {
	fn on_register(
		&self,
		providers: &InherentDataProviders,
	) -> result::Result<(), RuntimeString> {
		if !providers.has_provider(&timestamp::INHERENT_IDENTIFIER) {
			// Add the timestamp inherent data provider, as we require it.
			providers.register_provider(timestamp::InherentDataProvider)
		} else {
			Ok(())
		}
	}

	fn inherent_identifier(&self) -> &'static inherents::InherentIdentifier {
		&INHERENT_IDENTIFIER
	}

	fn provide_inherent_data(
		&self,
		inherent_data: &mut InherentData,
	) -> result::Result<(), RuntimeString> {
		let timestamp = inherent_data.timestamp_inherent_data()?;
		let slot_num = timestamp / self.slot_duration;
		inherent_data.put_data(INHERENT_IDENTIFIER, &slot_num)
	}

	fn error_to_string(&self, error: &[u8]) -> Option<String> {
		RuntimeString::decode(&mut &error[..]).map(Into::into)
	}
}

/// Something which can handle Aura consensus reports.
pub trait HandleReport {
	fn handle_report(report: AuraReport);
}

impl HandleReport for () {
	fn handle_report(_report: AuraReport) { }
}

pub trait Trait: timestamp::Trait {
	/// The logic for handling reports.
	type HandleReport: HandleReport;
}

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
#[derive(Clone, Encode, Decode, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct AuraReport {
	// The first skipped slot.
	start_slot: usize,
	// The number of times authorities were skipped.
	skipped: usize,
}

impl AuraReport {
	/// Call the closure with (validator_indices, punishment_count) for each
	/// validator to punish.
	pub fn punish<F>(&self, validator_count: usize, mut punish_with: F)
		where F: FnMut(usize, usize)
	{
		let start_slot = self.start_slot % validator_count;

		// the number of times everyone was skipped.
		let skipped_all = self.skipped / validator_count;
		// the number of validators who were skipped once after that.
		let skipped_after = self.skipped % validator_count;

		let iter = (start_slot..validator_count).into_iter()
			.chain(0..start_slot)
			.enumerate();

		for (rel_index, actual_index) in iter {
			let slash_count = skipped_all + if rel_index < skipped_after {
				1
			} else {
				// avoid iterating over all authorities when skipping a couple.
				if skipped_all == 0 { break }
				0
			};

			if slash_count > 0 {
				punish_with(actual_index, slash_count);
			}
		}
	}
}

impl<T: Trait> Module<T> {
	/// Determine the Aura slot-duration based on the timestamp module configuration.
	pub fn slot_duration() -> u64 {
		// we double the minimum block-period so each author can always propose within
		// the majority of their slot.
		<timestamp::Module<T>>::block_period().as_().saturating_mul(2)
	}

	fn on_timestamp_set<H: HandleReport>(now: T::Moment, slot_duration: T::Moment) {
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

		H::handle_report(AuraReport {
			start_slot: slot_to_usize(first_skipped),
			skipped: slot_to_usize(skipped_slots),
		})
	}
}

impl<T: Trait> OnTimestampSet<T::Moment> for Module<T> {
	fn on_timestamp_set(moment: T::Moment) {
		Self::on_timestamp_set::<T::HandleReport>(moment, T::Moment::sa(Self::slot_duration()))
	}
}

/// A type for performing slashing based on aura reports.
pub struct StakingSlasher<T>(::rstd::marker::PhantomData<T>);

impl<T: staking::Trait + Trait> HandleReport for StakingSlasher<T> {
	fn handle_report(report: AuraReport) {
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

impl<T: Trait> ProvideInherent for Module<T> {
	type Call = timestamp::Call<T>;
	type Error = MakeFatalError<RuntimeString>;
	const INHERENT_IDENTIFIER: InherentIdentifier = INHERENT_IDENTIFIER;

	fn create_inherent(_: &InherentData) -> Option<Self::Call> {
		None
	}

	fn check_inherent(call: &Self::Call, data: &InherentData) -> result::Result<(), Self::Error> {
		let timestamp = match call {
			timestamp::Call::set(ref timestamp) => timestamp.clone(),
			_ => return Ok(()),
		};

		let timestamp_based_slot = timestamp.as_() / Self::slot_duration();

		let seal_slot = data.aura_inherent_data()?;

		if timestamp_based_slot == seal_slot {
			Ok(())
		} else {
			Err(RuntimeString::from("timestamp set in block doesn't match slot in seal").into())
		}
	}
}
