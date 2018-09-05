// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Conensus module for runtime; manages the authority set ready for the native code.

#![cfg_attr(not(feature = "std"), no_std)]

#[allow(unused_imports)]
#[macro_use]
extern crate substrate_runtime_std as rstd;

#[macro_use]
extern crate substrate_runtime_support as runtime_support;

#[cfg(feature = "std")]
extern crate serde;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[macro_use]
extern crate substrate_codec_derive;

extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_primitives as primitives;
extern crate substrate_codec as codec;
extern crate substrate_runtime_system as system;
extern crate substrate_primitives;

use rstd::prelude::*;
use runtime_support::{storage, Parameter};
use runtime_support::dispatch::Result;
use runtime_support::storage::StorageValue;
use runtime_support::storage::unhashed::StorageVec;
use primitives::traits::{MaybeSerializeDebug, MaybeEmpty, OnFinalise, Member, AuthoritiesChangeDigest};
use primitives::bft::MisbehaviorReport;

#[cfg(any(feature = "std", test))]
use substrate_primitives::KeccakHasher;
#[cfg(any(feature = "std", test))]
use std::collections::HashMap;

pub const AUTHORITY_AT: &'static [u8] = b":auth:";
pub const AUTHORITY_COUNT: &'static [u8] = b":auth:len";

struct AuthorityStorageVec<S: codec::Codec + Default>(rstd::marker::PhantomData<S>);
impl<S: codec::Codec + Default> StorageVec for AuthorityStorageVec<S> {
	type Item = S;
	const PREFIX: &'static [u8] = AUTHORITY_AT;
}

pub const CODE: &'static [u8] = b":code";

pub type KeyValue = (Vec<u8>, Vec<u8>);

pub trait OnOfflineValidator {
	fn on_offline_validator(validator_index: usize);
}

impl OnOfflineValidator for () {
	fn on_offline_validator(_validator_index: usize) {}
}

pub type Log<T> = RawLog<
	<T as Trait>::SessionKey,
>;

/// An logs in this module.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
pub enum RawLog<SessionKey> {
	/// Authorities set has been changed. Contains the new set of authorities.
	AuthoritiesChange(AuthoritiesChange<SessionKey>),
}

impl<SessionKey> RawLog<SessionKey> {
	/// Try to cast the log entry as AuthoritiesChange log entry.
	pub fn as_authorities_change(&self) -> Option<&AuthoritiesChange<SessionKey>> {
		match *self {
			RawLog::AuthoritiesChange(ref item) => Some(item),
		}
	}
}

/// Authorities change log entry.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
pub struct AuthoritiesChange<SessionKey> {
	/// New set of authorities.
	pub new_authorities: Vec<SessionKey>,
}

// Implementation for tests outside of this crate.
impl<N> From<RawLog<N>> for u64 {
	fn from(log: RawLog<N>) -> u64 {
		match log {
			RawLog::AuthoritiesChange(_) => 1,
		}
	}
}

impl<SessionKey: Member> AuthoritiesChangeDigest for AuthoritiesChange<SessionKey> {
	type AuthorityId = SessionKey;

	fn authorities(&self) -> &[Self::AuthorityId] {
		&self.new_authorities
	}
}

pub trait Trait: system::Trait {
	/// The allowed extrinsic position for `note_offline` inherent.
	const NOTE_OFFLINE_POSITION: u32;

	/// Type for all log entries of this module.
	type Log: From<Log<Self>> + Into<system::DigestItemOf<Self>>;

	type SessionKey: Parameter + Default + MaybeSerializeDebug;
	type OnOfflineValidator: OnOfflineValidator;
}

decl_storage! {
	trait Store for Module<T: Trait> as Consensus {
		// Authorities set actual at the block execution start. IsSome only if
		// the set has been changed.
		OriginalAuthorities: Vec<T::SessionKey>;
	}
}

decl_module! {
	pub struct Module<T: Trait>;

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum Call where aux: T::PublicAux {
		fn report_misbehavior(aux, report: MisbehaviorReport<T::Hash, T::BlockNumber>) -> Result;
		fn note_offline(aux, offline_val_indices: Vec<u32>) -> Result;
		fn remark(aux, remark: Vec<u8>) -> Result;
	}

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum PrivCall {
		fn set_code(new: Vec<u8>) -> Result;
		fn set_storage(items: Vec<KeyValue>) -> Result;
	}
}

impl<T: Trait> Module<T> {
	/// Get the current set of authorities. These are the session keys.
	pub fn authorities() -> Vec<T::SessionKey> {
		AuthorityStorageVec::<T::SessionKey>::items()
	}

	/// Set the new code.
	fn set_code(new: Vec<u8>) -> Result {
		storage::unhashed::put_raw(CODE, &new);
		Ok(())
	}

	/// Set some items of storage.
	fn set_storage(items: Vec<KeyValue>) -> Result {
		for i in &items {
			storage::unhashed::put_raw(&i.0, &i.1);
		}
		Ok(())
	}

	/// Report some misbehaviour.
	fn report_misbehavior(_aux: &T::PublicAux, _report: MisbehaviorReport<T::Hash, T::BlockNumber>) -> Result {
		// TODO.
		Ok(())
	}

	/// Note the previous block's validator missed their opportunity to propose a block. This only comes in
	/// if 2/3+1 of the validators agree that no proposal was submitted. It's only relevant
	/// for the previous block.
	fn note_offline(aux: &T::PublicAux, offline_val_indices: Vec<u32>) -> Result {
		assert!(aux.is_empty());
		assert!(
			<system::Module<T>>::extrinsic_index() == Some(T::NOTE_OFFLINE_POSITION),
			"note_offline extrinsic must be at position {} in the block",
			T::NOTE_OFFLINE_POSITION
		);

		for validator_index in offline_val_indices.into_iter() {
			T::OnOfflineValidator::on_offline_validator(validator_index as usize);
		}
		
		Ok(())
	}

	/// Make some on-chain remark.
	fn remark(_aux: &T::PublicAux, _remark: Vec<u8>) -> Result {
		Ok(())
	}

	/// Set the current set of authorities' session keys.
	///
	/// Called by `next_session` only.
	pub fn set_authorities(authorities: &[T::SessionKey]) {
		let current_authorities = AuthorityStorageVec::<T::SessionKey>::items();
		if current_authorities != authorities {
			Self::save_original_authorities(Some(current_authorities));
			AuthorityStorageVec::<T::SessionKey>::set_items(authorities);
		}
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
}

/// Finalization hook for the consensus module.
impl<T: Trait> OnFinalise<T::BlockNumber> for Module<T> {
	fn on_finalise(_n: T::BlockNumber) {
		if let Some(_) = <OriginalAuthorities<T>>::take() {
			// TODO: call Self::deposit_log
		}
	}
}

#[cfg(any(feature = "std", test))]
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct GenesisConfig<T: Trait> {
	pub authorities: Vec<T::SessionKey>,
	#[serde(with = "substrate_primitives::bytes")]
	pub code: Vec<u8>,
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		GenesisConfig {
			authorities: vec![],
			code: vec![],
		}
	}
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> primitives::BuildStorage for GenesisConfig<T>
{
	fn build_storage(self) -> ::std::result::Result<HashMap<Vec<u8>, Vec<u8>>, String> {
		use codec::{Encode, KeyedVec};
		let auth_count = self.authorities.len() as u32;
		let mut r: runtime_io::TestExternalities<KeccakHasher> = self.authorities.into_iter().enumerate().map(|(i, v)|
			((i as u32).to_keyed_vec(AUTHORITY_AT), v.encode())
		).collect();
		r.insert(AUTHORITY_COUNT.to_vec(), auth_count.encode());
		r.insert(CODE.to_vec(), self.code);
		Ok(r.into())
	}
}
