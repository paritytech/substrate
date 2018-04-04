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

#[cfg_attr(test, macro_use)]
extern crate substrate_runtime_std as rstd;

#[macro_use]
extern crate substrate_runtime_support as runtime_support;

#[cfg(test)]
extern crate substrate_runtime_io as runtime_io;

extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_codec as codec;

use runtime_support::{StorageValue, Parameter};
use runtime_primitives::traits::HasPublicAux;

pub trait Trait: HasPublicAux {
	type Value: Parameter + Default;
}

decl_module! {
	pub struct Module<T: Trait>;
	pub enum Call where aux: T::PublicAux {
		fn set(aux, now: T::Value) = 0;
	}
}

decl_storage! {
	pub trait Store for Module<T: Trait>;
	pub Now get(now): b"tim:val" => required T::Value;
}

impl<T: Trait> Module<T> {
	pub fn get() -> T::Value {
		<Self as Store>::Now::get()
	}

	/// Set the current time.
	fn set(_aux: &T::PublicAux, now: T::Value) {
		<Self as Store>::Now::put(now);
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use codec::Joiner;
	use runtime_support::storage::StorageValue;

	struct TraitImpl;
	impl HasPublicAux for TraitImpl {
		type PublicAux = u64;
	}
	impl Trait for TraitImpl {
		type Value = u64;
	}
	type Timestamp = Module<TraitImpl>;

	#[test]
	fn timestamp_works() {

		let mut t: TestExternalities = map![
			twox_128(<Timestamp as Store>::Now::key()).to_vec() => vec![].and(&42u64)
		];

		with_externalities(&mut t, || {
			assert_eq!(<Timestamp as Store>::Now::get(), 42);
			Timestamp::aux_dispatch(Call::set(69), &0);
			assert_eq!(Timestamp::now(), 69);
		});
	}
}
