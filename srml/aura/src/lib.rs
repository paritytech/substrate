// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! # Aura Module
//!
//! - [`aura::Trait`](./trait.Trait.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Overview
//!
//! The Aura module extends Aura consensus by managing offline reporting.
//!
//! ## Interface
//!
//! ### Public Functions
//!
//! - `slot_duration` - Determine the Aura slot-duration based on the Timestamp module configuration.
//!
//! ## Related Modules
//!
//! - [Staking](../srml_staking/index.html): The Staking module is called in Aura to enforce slashing
//!  if validators miss a certain number of slots (see the [`StakingSlasher`](./struct.StakingSlasher.html)
//!  struct and associated method).
//! - [Timestamp](../srml_timestamp/index.html): The Timestamp module is used in Aura to track
//! consensus rounds (via `slots`).
//! - [Consensus](../srml_consensus/index.html): The Consensus module does not relate directly to Aura,
//!  but serves to manage offline reporting by implementing `ProvideInherent` in a similar way.
//!
//! ## References
//!
//! If you're interested in hacking on this module, it is useful to understand the interaction with
//! `substrate/core/inherents/src/lib.rs` and, specifically, the required implementation of
//! [`ProvideInherent`](../substrate_inherents/trait.ProvideInherent.html) and
//! [`ProvideInherentData`](../substrate_inherents/trait.ProvideInherentData.html) to create and check inherents.

#![cfg_attr(not(feature = "std"), no_std)]

pub use timestamp;

use rstd::{result, prelude::*};
use parity_codec::Encode;
use srml_support::{decl_storage, decl_module, Parameter, storage::StorageValue};
use primitives::{traits::{SaturatedConversion, Saturating, Zero, One, Member}, generic::DigestItem};
use timestamp::OnTimestampSet;
#[cfg(feature = "std")]
use timestamp::TimestampInherentData;
use inherents::{RuntimeString, InherentIdentifier, InherentData, ProvideInherent, MakeFatalError};
#[cfg(feature = "std")]
use inherents::{InherentDataProviders, ProvideInherentData};
use substrate_consensus_aura_primitives::{AURA_ENGINE_ID, ConsensusLog};
#[cfg(feature = "std")]
use parity_codec::Decode;

mod mock;
mod tests;

/// The Aura inherent identifier.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"auraslot";

/// The type of the Aura inherent.
pub type InherentType = u64;

/// Auxiliary trait to extract Aura inherent data.
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

/// Something that can handle Aura consensus reports.
pub trait HandleReport {
	fn handle_report(report: AuraReport);
}

impl HandleReport for () {
	fn handle_report(_report: AuraReport) { }
}

pub trait Trait: timestamp::Trait {
	/// The logic for handling reports.
	type HandleReport: HandleReport;

	/// The identifier type for an authority.
	type AuthorityId: Member + Parameter + Default;
}

decl_storage! {
	trait Store for Module<T: Trait> as Aura {
		/// The last timestamp.
		LastTimestamp get(last) build(|_| 0.into()): T::Moment;

		/// The current authorities
		pub Authorities get(authorities) config(): Vec<T::AuthorityId>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin { }
}

impl<T: Trait> Module<T> {
	fn change_authorities(new: Vec<T::AuthorityId>) {
		<Authorities<T>>::put(&new);

		let log: DigestItem<T::Hash> = DigestItem::Consensus(
			AURA_ENGINE_ID,
			ConsensusLog::AuthoritiesChange(new).encode()
		);
		<system::Module<T>>::deposit_log(log.into());
	}
}

impl<T: Trait> session::OneSessionHandler<T::AccountId> for Module<T> {
	type Key = T::AuthorityId;
	fn on_new_session<'a, I: 'a>(changed: bool, validators: I)
		where I: Iterator<Item=(&'a T::AccountId, T::AuthorityId)>
	{
		// instant changes
		if changed {
			let next_authorities = validators.map(|(_, k)| k).collect::<Vec<_>>();
			let last_authorities = <Module<T>>::authorities();
			if next_authorities != last_authorities {
				Self::change_authorities(next_authorities);
			}
		}
	}
	fn on_disabled(_i: usize) {
		// ignore?
	}
}

/// A report of skipped authorities in Aura.
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct AuraReport {
	// The first skipped slot.
	start_slot: usize,
	// The number of times authorities were skipped.
	skipped: usize,
}

impl AuraReport {
	/// Call the closure with (`validator_indices`, `punishment_count`) for each
	/// validator to punish.
	pub fn punish<F>(&self, validator_count: usize, mut punish_with: F)
		where F: FnMut(usize, usize)
	{
		// If all validators have been skipped, then it implies some sort of
		// systematic problem common to all rather than a minority of validators
		// not fulfilling their specific duties. In this case, it doesn't make
		// sense to punish anyone, so we guard against it.
		if self.skipped < validator_count {
			for index in 0..self.skipped {
				punish_with((self.start_slot + index) % validator_count, 1);
			}
		}
	}
}

impl<T: Trait> Module<T> {
	/// Determine the Aura slot-duration based on the Timestamp module configuration.
	pub fn slot_duration() -> T::Moment {
		// we double the minimum block-period so each author can always propose within
		// the majority of its slot.
		<timestamp::Module<T>>::minimum_period().saturating_mul(2.into())
	}

	fn on_timestamp_set<H: HandleReport>(now: T::Moment, slot_duration: T::Moment) {
		let last = Self::last();
		<Self as Store>::LastTimestamp::put(now.clone());

		if last.is_zero() {
			return;
		}

		assert!(!slot_duration.is_zero(), "Aura slot duration cannot be zero.");

		let last_slot = last / slot_duration.clone();
		let first_skipped = last_slot.clone() + One::one();
		let cur_slot = now / slot_duration;

		assert!(last_slot < cur_slot, "Only one block may be authored per slot.");
		if cur_slot == first_skipped { return }

		let skipped_slots = cur_slot - last_slot - One::one();

		H::handle_report(AuraReport {
			start_slot: first_skipped.saturated_into::<usize>(),
			skipped: skipped_slots.saturated_into::<usize>(),
		})
	}
}

impl<T: Trait> OnTimestampSet<T::Moment> for Module<T> {
	fn on_timestamp_set(moment: T::Moment) {
		Self::on_timestamp_set::<T::HandleReport>(moment, Self::slot_duration())
	}
}

/// A type for performing slashing based on Aura reports.
pub struct StakingSlasher<T>(::rstd::marker::PhantomData<T>);

impl<T: staking::Trait + Trait> HandleReport for StakingSlasher<T> {
	fn handle_report(report: AuraReport) {
		let validators = session::Module::<T>::validators();

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

	/// Verify the validity of the inherent using the timestamp.
	fn check_inherent(call: &Self::Call, data: &InherentData) -> result::Result<(), Self::Error> {
		let timestamp = match call {
			timestamp::Call::set(ref timestamp) => timestamp.clone(),
			_ => return Ok(()),
		};

		let timestamp_based_slot = timestamp / Self::slot_duration();

		let seal_slot = data.aura_inherent_data()?.saturated_into();

		if timestamp_based_slot == seal_slot {
			Ok(())
		} else {
			Err(RuntimeString::from("timestamp set in block doesn't match slot in seal").into())
		}
	}
}
