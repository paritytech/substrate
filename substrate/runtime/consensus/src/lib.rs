// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

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

extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_primitives as primitives;
extern crate substrate_codec as codec;
extern crate substrate_runtime_system as system;
extern crate substrate_primitives;

use rstd::prelude::*;
use runtime_support::{storage, Parameter};
use runtime_support::dispatch::Result;
use runtime_support::storage::unhashed::StorageVec;
use primitives::traits::{RefInto, MaybeSerializeDebug, MaybeEmpty};
use primitives::bft::MisbehaviorReport;

pub const AUTHORITY_AT: &'static [u8] = b":auth:";
pub const AUTHORITY_COUNT: &'static [u8] = b":auth:len";

struct AuthorityStorageVec<S: codec::Slicable + Default>(rstd::marker::PhantomData<S>);
impl<S: codec::Slicable + Default> StorageVec for AuthorityStorageVec<S> {
	type Item = S;
	const PREFIX: &'static [u8] = AUTHORITY_AT;
}

pub const CODE: &'static [u8] = b":code";

pub type KeyValue = (Vec<u8>, Vec<u8>);

pub trait Trait: system::Trait {
	type PublicAux: RefInto<Self::AccountId> + MaybeEmpty;		// MaybeEmpty is for Timestamp's usage.
	type SessionKey: Parameter + Default + MaybeSerializeDebug;
}

decl_module! {
	pub struct Module<T: Trait>;

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum Call where aux: T::PublicAux {
		fn report_misbehavior(aux, report: MisbehaviorReport<T::Hash, T::BlockNumber>) -> Result = 0;
		fn remark(aux, remark: Vec<u8>) -> Result = 1;
	}

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum PrivCall {
		fn set_code(new: Vec<u8>) -> Result = 0;
		fn set_storage(items: Vec<KeyValue>) -> Result = 1;
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

	/// Make some on-chain remark.
	fn remark(_aux: &T::PublicAux, _remark: Vec<u8>) -> Result {
		Ok(())
	}

	/// Set the current set of authorities' session keys.
	///
	/// Called by `next_session` only.
	pub fn set_authorities(authorities: &[T::SessionKey]) {
		AuthorityStorageVec::<T::SessionKey>::set_items(authorities);
	}

	/// Set a single authority by index.
	pub fn set_authority(index: u32, key: &T::SessionKey) {
		AuthorityStorageVec::<T::SessionKey>::set_item(index, key);
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
	fn build_storage(self) -> ::std::result::Result<runtime_io::TestExternalities, String> {
		use codec::{Slicable, KeyedVec};
		let auth_count = self.authorities.len() as u32;
		let mut r: runtime_io::TestExternalities = self.authorities.into_iter().enumerate().map(|(i, v)|
			((i as u32).to_keyed_vec(AUTHORITY_AT), v.encode())
		).collect();
		r.insert(AUTHORITY_COUNT.to_vec(), auth_count.encode());
		r.insert(CODE.to_vec(), self.code);
		Ok(r)
	}
}
