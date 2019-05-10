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

//! # Consensus Module
//!
//! - [`consensus::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Overview
//!
//! The consensus module manages the authority set for the native code. It provides support for reporting offline
//! behavior among validators and logging changes in the validator authority set.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! - `report_misbehavior` - Report some misbehavior. The origin of this call must be signed.
//! - `note_offline` - Note that the previous block's validator missed its opportunity to propose a block.
//!  The origin of this call must be an inherent.
//! - `remark` - Make some on-chain remark. The origin of this call must be signed.
//! - `set_heap_pages` - Set the number of pages in the WebAssembly environment's heap.
//! - `set_code` - Set the new code.
//! - `set_storage` - Set some items of storage.
//!
//! ### Public Functions
//!
//! - `authorities` - Get the current set of authorities. These are the session keys.
//! - `set_authorities` - Set the current set of authorities' session keys.
//! - `set_authority_count` - Set the total number of authorities.
//! - `set_authority` - Set a single authority by index.
//!
//! ## Usage
//!
//! ### Simple Code Snippet
//!
//! Set authorities:
//!
//! ```
//! # use srml_consensus as consensus;
//! # fn not_executed<T: consensus::Trait>() {
//! # let authority1 = T::SessionKey::default();
//! # let authority2 = T::SessionKey::default();
//! <consensus::Module<T>>::set_authorities(&[authority1, authority2])
//! # }
//! ```
//!
//! Log changes in the authorities set:
//!
//! ```
//! # use srml_consensus as consensus;
//! # use primitives::traits::Zero;
//! # use primitives::traits::OnFinalize;
//! # fn not_executed<T: consensus::Trait>() {
//! <consensus::Module<T>>::on_finalize(T::BlockNumber::zero());
//! # }
//! ```
//!
//! ### Example from SRML
//!
//! In the staking module, the `consensus::OnOfflineReport` is implemented to monitor offline
//! reporting among validators:
//!
//! ```
//! # use srml_consensus as consensus;
//! # trait Trait: consensus::Trait {
//! # }
//! #
//! # srml_support::decl_module! {
//! #     pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//! #     }
//! # }
//! #
//! impl<T: Trait> consensus::OnOfflineReport<Vec<u32>> for Module<T> {
//! 	fn handle_report(reported_indices: Vec<u32>) {
//! 		for validator_index in reported_indices {
//! 			// Get validator from session module
//! 			// Process validator
//! 		}
//! 	}
//! }
//! ```
//!
//! In the GRANDPA module, we use `srml-consensus` to get the set of `next_authorities` before changing
//! this set according to the consensus algorithm (which does not rotate sessions in the *normal* way):
//!
//! ```
//! # use srml_consensus as consensus;
//! # use consensus::Trait;
//! # fn not_executed<T: consensus::Trait>() {
//! let next_authorities = <consensus::Module<T>>::authorities()
//! 			.into_iter()
//! 			.map(|key| (key, 1)) // evenly-weighted.
//! 			.collect::<Vec<(<T as Trait>::SessionKey, u64)>>();
//! # }
//! ```
//!
//! ## Related Modules
//!
//! - [Staking](../srml_staking/index.html): This module uses `srml-consensus` to monitor offline
//! reporting among validators.
//! - [Aura](../srml_aura/index.html): This module does not relate directly to `srml-consensus`,
//! but serves to manage offline reporting for the Aura consensus algorithm with its own `handle_report` method.
//! - [Grandpa](../srml_grandpa/index.html): Although GRANDPA does its own voter-set management,
//!  it has a mode where it can track `consensus`, if desired.
//!
//! ## References
//!
//! If you're interested in hacking on this module, it is useful to understand the interaction with
//! `substrate/core/inherents/src/lib.rs` and, specifically, the required implementation of `ProvideInherent`
//! to create and check inherents.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use serde::Serialize;
use rstd::prelude::*;
use parity_codec as codec;
use codec::{Encode, Decode};
use srml_support::{storage, Parameter, decl_storage, decl_module};
use srml_support::storage::StorageValue;
use srml_support::storage::unhashed::StorageVec;
use primitives::traits::{MaybeSerializeDebug, Member};
use substrate_primitives::storage::well_known_keys;
use system::{ensure_signed, ensure_none};
use inherents::{
	ProvideInherent, InherentData, InherentIdentifier, RuntimeString, MakeFatalError
};

#[cfg(any(feature = "std", test))]
use substrate_primitives::sr25519::Public as AuthorityId;

mod mock;
mod tests;

/// The identifier for consensus inherents.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"offlrep0";

/// The error type used by this inherent.
pub type InherentError = RuntimeString;

struct AuthorityStorageVec<S: codec::Codec + Default>(rstd::marker::PhantomData<S>);
impl<S: codec::Codec + Default> StorageVec for AuthorityStorageVec<S> {
	type Item = S;
	const PREFIX: &'static [u8] = well_known_keys::AUTHORITY_PREFIX;
}

pub type Key = Vec<u8>;
pub type KeyValue = (Vec<u8>, Vec<u8>);

/// Handling offline validator reports in a generic way.
pub trait OnOfflineReport<Offline> {
	fn handle_report(offline: Offline);
}

impl<T> OnOfflineReport<T> for () {
	fn handle_report(_: T) {}
}

/// Describes the offline-reporting extrinsic.
pub trait InherentOfflineReport {
	/// The report data type passed to the runtime during block authorship.
	type Inherent: codec::Codec + Parameter;

	/// Whether an inherent is empty and doesn't need to be included.
	fn is_empty(inherent: &Self::Inherent) -> bool;

	/// Handle the report.
	fn handle_report(report: Self::Inherent);

	/// Whether two reports are compatible.
	fn check_inherent(contained: &Self::Inherent, expected: &Self::Inherent) -> Result<(), &'static str>;
}

impl InherentOfflineReport for () {
	type Inherent = ();

	fn is_empty(_inherent: &()) -> bool { true }
	fn handle_report(_: ()) { }
	fn check_inherent(_: &(), _: &()) -> Result<(), &'static str> {
		Err("Explicit reporting not allowed")
	}
}

/// A variant of the `OfflineReport` that is useful for instant-finality blocks.
///
/// This assumes blocks are only finalized.
pub struct InstantFinalityReportVec<T>(::rstd::marker::PhantomData<T>);

impl<T: OnOfflineReport<Vec<u32>>> InherentOfflineReport for InstantFinalityReportVec<T> {
	type Inherent = Vec<u32>;

	fn is_empty(inherent: &Self::Inherent) -> bool { inherent.is_empty() }

	fn handle_report(report: Vec<u32>) {
		T::handle_report(report)
	}

	fn check_inherent(contained: &Self::Inherent, expected: &Self::Inherent) -> Result<(), &'static str> {
		contained.iter().try_for_each(|n|
			if !expected.contains(n) {
				Err("Node we believe online marked offline")
			} else {
				Ok(())
			}
		)
	}
}

pub type Log<T> = RawLog<
	<T as Trait>::SessionKey,
>;

/// Logs in this module.
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
pub enum RawLog<SessionKey> {
	/// Authorities set has been changed. Contains the new set of authorities.
	AuthoritiesChange(Vec<SessionKey>),
}

impl<SessionKey: Member> RawLog<SessionKey> {
	/// Try to cast the log entry as AuthoritiesChange log entry.
	pub fn as_authorities_change(&self) -> Option<&[SessionKey]> {
		match *self {
			RawLog::AuthoritiesChange(ref item) => Some(item),
		}
	}
}

// Implementation for tests outside of this crate.
#[cfg(any(feature = "std", test))]
impl<N> From<RawLog<N>> for primitives::testing::DigestItem where N: Into<AuthorityId> {
	fn from(log: RawLog<N>) -> primitives::testing::DigestItem {
		match log {
			RawLog::AuthoritiesChange(authorities) =>
				primitives::generic::DigestItem::AuthoritiesChange(
					authorities.into_iter()
						.map(Into::into).collect()),
		}
	}
}

pub trait Trait: system::Trait {
	/// Type for all log entries of this module.
	type Log: From<Log<Self>> + Into<system::DigestItemOf<Self>>;

	type SessionKey: Parameter + Default + MaybeSerializeDebug;
	/// Defines the offline-report type of the trait.
	/// Set to `()` if offline-reports aren't needed for this runtime.
	type InherentOfflineReport: InherentOfflineReport;
}

decl_storage! {
	trait Store for Module<T: Trait> as Consensus {
		// Actual authorities set at the block execution start. Is `Some` iff
		// the set has been changed.
		OriginalAuthorities: Option<Vec<T::SessionKey>>;
	}
	add_extra_genesis {
		config(authorities): Vec<T::SessionKey>;
		#[serde(with = "substrate_primitives::bytes")]
		config(code): Vec<u8>;

		build(|storage: &mut primitives::StorageOverlay, _: &mut primitives::ChildrenStorageOverlay, config: &GenesisConfig<T>| {
			use codec::{Encode, KeyedVec};

			let auth_count = config.authorities.len() as u32;
			config.authorities.iter().enumerate().for_each(|(i, v)| {
				storage.insert((i as u32).to_keyed_vec(well_known_keys::AUTHORITY_PREFIX), v.encode());
			});
			storage.insert(well_known_keys::AUTHORITY_COUNT.to_vec(), auth_count.encode());
			storage.insert(well_known_keys::CODE.to_vec(), config.code.clone());
		});
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Report some misbehavior.
		fn report_misbehavior(origin, _report: Vec<u8>) {
			ensure_signed(origin)?;
		}

		/// Note that the previous block's validator missed its opportunity to propose a block.
		fn note_offline(origin, offline: <T::InherentOfflineReport as InherentOfflineReport>::Inherent) {
			ensure_none(origin)?;

			T::InherentOfflineReport::handle_report(offline);
		}

		/// Make some on-chain remark.
		fn remark(origin, _remark: Vec<u8>) {
			ensure_signed(origin)?;
		}

		/// Set the number of pages in the WebAssembly environment's heap.
		fn set_heap_pages(pages: u64) {
			storage::unhashed::put_raw(well_known_keys::HEAP_PAGES, &pages.encode());
		}

		/// Set the new code.
		pub fn set_code(new: Vec<u8>) {
			storage::unhashed::put_raw(well_known_keys::CODE, &new);
		}

		/// Set some items of storage.
		fn set_storage(items: Vec<KeyValue>) {
			for i in &items {
				storage::unhashed::put_raw(&i.0, &i.1);
			}
		}

		/// Kill some items from storage.
		fn kill_storage(keys: Vec<Key>) {
			for key in &keys {
				storage::unhashed::kill(&key);
			}
		}

		fn on_finalize() {
			if let Some(original_authorities) = <OriginalAuthorities<T>>::take() {
				let current_authorities = AuthorityStorageVec::<T::SessionKey>::items();
				if current_authorities != original_authorities {
					Self::deposit_log(RawLog::AuthoritiesChange(current_authorities));
				}
			}
		}
	}
}

impl<T: Trait> Module<T> {
	/// Get the current set of authorities. These are the session keys.
	pub fn authorities() -> Vec<T::SessionKey> {
		AuthorityStorageVec::<T::SessionKey>::items()
	}

	/// Set the current set of authorities' session keys. Will not exceed the current
	/// authorities count, even if the given `authorities` is longer.
	///
	/// Called by `rotate_session` only.
	pub fn set_authorities(authorities: &[T::SessionKey]) {
		let current_authorities = AuthorityStorageVec::<T::SessionKey>::items();
		if current_authorities != authorities {
			Self::save_original_authorities(Some(current_authorities));
			AuthorityStorageVec::<T::SessionKey>::set_items(authorities);
		}
	}

	/// Set the total number of authorities.
	pub fn set_authority_count(count: u32) {
		Self::save_original_authorities(None);
		AuthorityStorageVec::<T::SessionKey>::set_count(count);
	}

	/// Set a single authority by index.
	pub fn set_authority(index: u32, key: &T::SessionKey) {
		let current_authority = AuthorityStorageVec::<T::SessionKey>::item(index);
		if current_authority != *key {
			Self::save_original_authorities(None);
			AuthorityStorageVec::<T::SessionKey>::set_item(index, key);
		}
	}

	/// Save original authorities set.
	fn save_original_authorities(current_authorities: Option<Vec<T::SessionKey>>) {
		if OriginalAuthorities::<T>::get().is_some() {
			// if we have already saved original set before, do not overwrite
			return;
		}

		<OriginalAuthorities<T>>::put(current_authorities.unwrap_or_else(||
			AuthorityStorageVec::<T::SessionKey>::items()));
	}

	/// Deposit one of this module's logs.
	fn deposit_log(log: Log<T>) {
		<system::Module<T>>::deposit_log(<T as Trait>::Log::from(log).into());
	}
}

/// Implementing `ProvideInherent` enables this module to create and check inherents.
impl<T: Trait> ProvideInherent for Module<T> {
	/// The call type of the module.
	type Call = Call<T>;
	/// The error returned by `check_inherent`.
	type Error = MakeFatalError<RuntimeString>;
	/// The inherent identifier used by this inherent.
	const INHERENT_IDENTIFIER: InherentIdentifier = INHERENT_IDENTIFIER;

	/// Creates an inherent from the `InherentData`.
	fn create_inherent(data: &InherentData) -> Option<Self::Call> {
		if let Ok(Some(data)) =
			data.get_data::<<T::InherentOfflineReport as InherentOfflineReport>::Inherent>(
				&INHERENT_IDENTIFIER
			)
		{
			if <T::InherentOfflineReport as InherentOfflineReport>::is_empty(&data) {
				None
			} else {
				Some(Call::note_offline(data))
			}
		} else {
			None
		}
	}

	/// Verify the validity of the given inherent.
	fn check_inherent(call: &Self::Call, data: &InherentData) -> Result<(), Self::Error> {
		let offline = match call {
			Call::note_offline(ref offline) => offline,
			_ => return Ok(()),
		};

		let expected = data
			.get_data::<<T::InherentOfflineReport as InherentOfflineReport>::Inherent>(&INHERENT_IDENTIFIER)?
			.ok_or(RuntimeString::from("No `offline_report` found in the inherent data!"))?;

		<T::InherentOfflineReport as InherentOfflineReport>::check_inherent(
			&offline, &expected
		).map_err(|e| RuntimeString::from(e).into())
	}
}
