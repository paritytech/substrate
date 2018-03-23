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

//! Timestamp manager: just handles the current timestamp.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg_attr(test, macro_use)] extern crate substrate_runtime_std as rstd;
#[macro_use] extern crate substrate_runtime_support as runtime_support;
#[cfg(test)] extern crate substrate_runtime_io as runtime_io;
extern crate substrate_codec as codec;

#[cfg(feature = "std")] #[macro_use] extern crate serde_derive;
#[cfg(feature = "std")] extern crate serde;

use runtime_support::storage::StorageValue;
use runtime_support::PublicPass;

pub trait Trait {
	type Timestamp: codec::Slicable + Default;
	type PublicAux;
	type PrivAux;
}
pub struct Module<T: Trait>(::std::marker::PhantomData<T>);

// TODO: create from storage_items macro.
decl_storage! {
	trait Trait as T;
	pub store Store for Module;
	pub Now: b"tim:val" => required T::Timestamp;
	Then: b"tim:then" => default T::Timestamp;
}
impl<T: Trait> Module<T> {
	pub fn get() -> T::Timestamp { <Now<T>>::get() }
}

// TODO: implement `Callable` and `Dispatch` in `impl_dispatch` macro.
/*
impl_dispatch! {
	trait Trait;
	pub mod public;
	fn set(_, now: Timestamp) = 0;
}
*/

pub trait Dispatchable {
	type AuxType;
	type TraitType;
	fn dispatch(self, aux: &Self::AuxType);
}

pub mod public {
	use super::Trait;
	pub enum Callable<T: Trait> { set(T::Timestamp) }
	pub trait Dispatch<T: Trait> { fn set(aux: &T::PublicAux, now: T::Timestamp); }

	impl<T: Trait> super::Dispatchable for Callable<T> where super::Module<T>: Dispatch<T> {
		type TraitType = T;
		type AuxType = T::PublicAux;
		fn dispatch(self, aux: &Self::AuxType) {
			match self {
				Callable::set(a) => <super::Module<T>>::set(aux, a),
			}
		}
	}
}

impl<T: Trait> public::Dispatch<T> for Module<T> {
	/// Set the current time.
	fn set(_aux: &T::PublicAux, now: T::Timestamp) {
		<Self as Store>::Now::put(now);
	}
}

impl<T: Trait> Module<T> {
	pub fn dispatch<D: Dispatchable<TraitType = T>>(d: D, aux: &D::AuxType) {
		d.dispatch(aux);
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use codec::Joiner;
	use runtime_support::storage::StorageValue;
	use runtime_support::PublicPass;

	struct TraitImpl;
	impl super::Trait for TraitImpl {
		type Timestamp = u64;
		type PublicAux = u64;
		type PrivAux = ();
	}
	type Timestamp = super::Module<TraitImpl>;

	#[test]
	fn timestamp_works() {

		let mut t: TestExternalities = map![
			twox_128(<Timestamp as Store>::Now::key()).to_vec() => vec![].and(&42u64)
		];

		with_externalities(&mut t, || {
			assert_eq!(<Timestamp as Store>::Now::get(), 42);
//			assert_eq!(Timestamp::NOW.get(), 42);
			Timestamp::dispatch(public::Callable::set(69), &0);
			assert_eq!(<Timestamp as Store>::Now::get(), 69);
//			assert_eq!(Timestamp::NOW.get(), 69);
		});
	}
}
