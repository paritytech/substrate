// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! # Aura Module
//!
//! - [`aura::Config`](./trait.Config.html)
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
//! - [Timestamp](../pallet_timestamp/index.html): The Timestamp module is used in Aura to track
//! consensus rounds (via `slots`).
//!
//! ## References
//!
//! If you're interested in hacking on this module, it is useful to understand the interaction with
//! `substrate/primitives/inherents/src/lib.rs` and, specifically, the required implementation of
//! [`ProvideInherent`](../sp_inherents/trait.ProvideInherent.html) and
//! [`ProvideInherentData`](../sp_inherents/trait.ProvideInherentData.html) to create and check inherents.

#![cfg_attr(not(feature = "std"), no_std)]

use pallet_timestamp;

use sp_std::{result, prelude::*};
use codec::{Encode, Decode};
use frame_support::{
	decl_storage, decl_module, Parameter, traits::{Get, FindAuthor},
	ConsensusEngineId,
};
use sp_runtime::{
	RuntimeAppPublic,
	traits::{SaturatedConversion, Saturating, Zero, Member, IsMember}, generic::DigestItem,
};
use sp_timestamp::OnTimestampSet;
use sp_inherents::{InherentIdentifier, InherentData, ProvideInherent, MakeFatalError};
use sp_consensus_aura::{
	AURA_ENGINE_ID, ConsensusLog, AuthorityIndex,
	inherents::{INHERENT_IDENTIFIER, AuraInherentData},
};

mod mock;
mod tests;

pub trait Config: pallet_timestamp::Config {
	/// The identifier type for an authority.
	type AuthorityId: Member + Parameter + RuntimeAppPublic + Default;
}

decl_storage! {
	trait Store for Module<T: Config> as Aura {
		/// The last timestamp.
		LastTimestamp get(fn last): T::Moment;

		/// The current authorities
		pub Authorities get(fn authorities): Vec<T::AuthorityId>;
	}
	add_extra_genesis {
		config(authorities): Vec<T::AuthorityId>;
		build(|config| Module::<T>::initialize_authorities(&config.authorities))
	}
}

decl_module! {
	pub struct Module<T: Config> for enum Call where origin: T::Origin { }
}

impl<T: Config> Module<T> {
	fn change_authorities(new: Vec<T::AuthorityId>) {
		<Authorities<T>>::put(&new);

		let log: DigestItem<T::Hash> = DigestItem::Consensus(
			AURA_ENGINE_ID,
			ConsensusLog::AuthoritiesChange(new).encode()
		);
		<frame_system::Module<T>>::deposit_log(log.into());
	}

	fn initialize_authorities(authorities: &[T::AuthorityId]) {
		if !authorities.is_empty() {
			assert!(<Authorities<T>>::get().is_empty(), "Authorities are already initialized!");
			<Authorities<T>>::put(authorities);
		}
	}
}

impl<T: Config> sp_runtime::BoundToRuntimeAppPublic for Module<T> {
	type Public = T::AuthorityId;
}

impl<T: Config> pallet_session::OneSessionHandler<T::AccountId> for Module<T> {
	type Key = T::AuthorityId;

	fn on_genesis_session<'a, I: 'a>(validators: I)
		where I: Iterator<Item=(&'a T::AccountId, T::AuthorityId)>
	{
		let authorities = validators.map(|(_, k)| k).collect::<Vec<_>>();
		Self::initialize_authorities(&authorities);
	}

	fn on_new_session<'a, I: 'a>(changed: bool, validators: I, _queued_validators: I)
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

	fn on_disabled(i: usize) {
		let log: DigestItem<T::Hash> = DigestItem::Consensus(
			AURA_ENGINE_ID,
			ConsensusLog::<T::AuthorityId>::OnDisabled(i as AuthorityIndex).encode(),
		);

		<frame_system::Module<T>>::deposit_log(log.into());
	}
}

impl<T: Config> FindAuthor<u32> for Module<T> {
	fn find_author<'a, I>(digests: I) -> Option<u32> where
		I: 'a + IntoIterator<Item=(ConsensusEngineId, &'a [u8])>
	{
		for (id, mut data) in digests.into_iter() {
			if id == AURA_ENGINE_ID {
				if let Ok(slot_num) = u64::decode(&mut data) {
					let author_index = slot_num % Self::authorities().len() as u64;
					return Some(author_index as u32)
				}
			}
		}

		None
	}
}

/// We can not implement `FindAuthor` twice, because the compiler does not know if 
/// `u32 == T::AuthorityId` and thus, prevents us to implement the trait twice.
#[doc(hidden)]
pub struct FindAccountFromAuthorIndex<T, Inner>(sp_std::marker::PhantomData<(T, Inner)>);

impl<T: Config, Inner: FindAuthor<u32>> FindAuthor<T::AuthorityId>
	for FindAccountFromAuthorIndex<T, Inner>
{
	fn find_author<'a, I>(digests: I) -> Option<T::AuthorityId>
		where I: 'a + IntoIterator<Item=(ConsensusEngineId, &'a [u8])>
	{
		let i = Inner::find_author(digests)?;

		let validators = <Module<T>>::authorities();
		validators.get(i as usize).map(|k| k.clone())
	}
}

/// Find the authority ID of the Aura authority who authored the current block.
pub type AuraAuthorId<T> = FindAccountFromAuthorIndex<T, Module<T>>;

impl<T: Config> IsMember<T::AuthorityId> for Module<T> {
	fn is_member(authority_id: &T::AuthorityId) -> bool {
		Self::authorities()
			.iter()
			.any(|id| id == authority_id)
	}
}

impl<T: Config> Module<T> {
	/// Determine the Aura slot-duration based on the Timestamp module configuration.
	pub fn slot_duration() -> T::Moment {
		// we double the minimum block-period so each author can always propose within
		// the majority of its slot.
		<T as pallet_timestamp::Config>::MinimumPeriod::get().saturating_mul(2u32.into())
	}

	fn on_timestamp_set(now: T::Moment, slot_duration: T::Moment) {
		let last = Self::last();
		<Self as Store>::LastTimestamp::put(now);

		if last.is_zero() {
			return;
		}

		assert!(!slot_duration.is_zero(), "Aura slot duration cannot be zero.");

		let last_slot = last / slot_duration;
		let cur_slot = now / slot_duration;

		assert!(last_slot < cur_slot, "Only one block may be authored per slot.");

		// TODO [#3398] Generate offence report for all authorities that skipped their slots.
	}
}

impl<T: Config> OnTimestampSet<T::Moment> for Module<T> {
	fn on_timestamp_set(moment: T::Moment) {
		Self::on_timestamp_set(moment, Self::slot_duration())
	}
}

impl<T: Config> ProvideInherent for Module<T> {
	type Call = pallet_timestamp::Call<T>;
	type Error = MakeFatalError<sp_inherents::Error>;
	const INHERENT_IDENTIFIER: InherentIdentifier = INHERENT_IDENTIFIER;

	fn create_inherent(_: &InherentData) -> Option<Self::Call> {
		None
	}

	/// Verify the validity of the inherent using the timestamp.
	fn check_inherent(call: &Self::Call, data: &InherentData) -> result::Result<(), Self::Error> {
		let timestamp = match call {
			pallet_timestamp::Call::set(ref timestamp) => timestamp.clone(),
			_ => return Ok(()),
		};

		let timestamp_based_slot = timestamp / Self::slot_duration();

		let seal_slot = data.aura_inherent_data()?.saturated_into();

		if timestamp_based_slot == seal_slot {
			Ok(())
		} else {
			Err(sp_inherents::Error::from("timestamp set in block doesn't match slot in seal").into())
		}
	}
}
