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

//! A simple, secure module for dealing with fungible assets.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

// Assert macros used in tests.
extern crate sr_std;

// Needed for tests (`with_externalities`).
#[cfg(test)]
extern crate sr_io as runtime_io;

// Needed for the set of mock primitives used in our tests.
#[cfg(test)]
extern crate substrate_primitives;

// Needed for deriving `Serialize` and `Deserialize` for various types.
// We only implement the serde traits for std builds - they're unneeded
// in the wasm runtime.
#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

// Needed for deriving `Encode` and `Decode` for `RawEvent`.
#[macro_use]
extern crate parity_codec_derive;
extern crate parity_codec as codec;

// Needed for type-safe access to storage DB.
#[macro_use]
extern crate srml_support as runtime_support;

// Needed for various traits. In our case, `OnFinalise`.
extern crate sr_primitives as primitives;
// `system` module provides us with all sorts of useful stuff and macros
// depend on it being around.
extern crate srml_system as system;

use runtime_support::{StorageValue, StorageMap, dispatch::Result, Parameter};
use primitives::traits::{Member, SimpleArithmetic, Zero};
use system::ensure_signed;

pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// The units in which we record balances.
	type Balance: Member + Parameter + SimpleArithmetic + Default + Copy;
}

type AssetId = u32;

decl_module! {
	// Simple declaration of the `Module` type. Lets the macro know what its working on.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;
		/// Issue a new class of fungible assets. There are, and will only ever be, `total`
		/// such assets and they'll all belong to the `origin` initially. It will have an
		/// identifier `AssetId` instance: this will be specified in the `Issued` event.
		fn issue(origin, total: T::Balance) -> Result {
			let origin = ensure_signed(origin)?;

			let id = Self::next_asset_id();
			<NextAssetId<T>>::mutate(|id| *id += 1);

			<Balances<T>>::insert((id, origin.clone()), total);

			Self::deposit_event(RawEvent::Issued(id, origin, total));
			Ok(())
		}

		/// Move some assets from one holder to another.
		fn transfer(origin, id: AssetId, target: T::AccountId, amount: T::Balance) -> Result {
			let origin = ensure_signed(origin)?;
			let origin_account = (id, origin.clone());
			let origin_balance = <Balances<T>>::get(&origin_account);
			ensure!(origin_balance >= amount, "origin account balance must be greater than amount");

			Self::deposit_event(RawEvent::Transfered(id, origin, target.clone(), amount));
			<Balances<T>>::insert(origin_account, origin_balance - amount);
			<Balances<T>>::mutate((id, target), |balance| *balance += amount);

			Ok(())
		}

		/// Destroy any assets of `id` owned by `origin`.
		fn destroy(origin, id: AssetId) -> Result {
			let origin = ensure_signed(origin)?;

			let balance = <Balances<T>>::take((id, origin.clone()));
			ensure!(!balance.is_zero(), "origin balance should be non-zero");

			Self::deposit_event(RawEvent::Destroyed(id, origin, balance));

			Ok(())
		}
	}
}

/// An event in this module. Events are simple means of reporting specific conditions and
/// circumstances that have happened that users, Dapps and/or chain explorers would find
/// interesting and otherwise difficult to detect.
decl_event!(
	pub enum Event<T> where <T as system::Trait>::AccountId, <T as Trait>::Balance {
		/// Some assets were issued.
		Issued(AssetId, AccountId, Balance),
		/// Some assets were transfered.
		Transfered(AssetId, AccountId, AccountId, Balance),
		/// Some assets were destroyed.
		Destroyed(AssetId, AccountId, Balance),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as Assets {
		/// The number of units of assets held by any given account.
		Balances: map (AssetId, T::AccountId) => T::Balance;
		/// The next asset identifier up for grabs.
		NextAssetId get(next_asset_id): AssetId;
	}
}

// The main implementation block for the module.
impl<T: Trait> Module<T> {
	// Public immutables

	/// Get the asset `id` balance of `who`.
	pub fn balance(id: AssetId, who: T::AccountId) -> T::Balance {
		<Balances<T>>::get((id, who))
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use runtime_io::with_externalities;
	use substrate_primitives::{H256, Blake2Hasher};
	// The testing primitives are very useful for avoiding having to work with signatures
	// or public keys. `u64` is used as the `AccountId` and no `Signature`s are requried.
	use primitives::{BuildStorage, traits::{BlakeTwo256}, testing::{Digest, DigestItem, Header}};

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	// For testing the module, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of modules we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Header = Header;
		type Event = ();
		type Log = DigestItem;
	}
	impl Trait for Test {
		type Event = ();
		type Balance = u64;
	}
	type Assets = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		system::GenesisConfig::<Test>::default().build_storage().unwrap().0.into()
	}

	#[test]
	fn it_works() {
		with_externalities(&mut new_test_ext(), || {
			assert_ok!(Assets::issue(Origin::signed(1), 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 50));
			assert_eq!(Assets::balance(0, 1), 50);
			assert_eq!(Assets::balance(0, 2), 50);
			assert_ok!(Assets::destroy(Origin::signed(2), 0));
			assert_eq!(Assets::balance(0, 2), 0);
			assert_noop!(Assets::transfer(Origin::signed(2), 0, 1, 50), "origin account balance must be greater than amount");
		});
	}
}
