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

//! The Example: A simple example of a runtime module demonstrating
//! concepts, APIs and structures common to most runtime modules.

#![cfg_attr(not(feature = "std"), no_std)]

use sr_std::prelude::*;
use sr_primitives::traits::StaticLookup;
use srml_support::{decl_module, decl_event, ensure};
use storage::{StorageValue, decl_storage};
use system::ensure_signed;

pub trait Trait: consensus::Trait + system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

decl_module! {
	// Simple declaration of the `Module` type. Lets the macro know what its working on.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;
		fn upgrade(origin, new: Vec<u8>) {
			// This is a public call, so we ensure that the origin is some signed account.
			let _sender = ensure_signed(origin)?;
			ensure!(_sender == Self::key(), "only the current upgrade key can use the upgrade_key module");

			<consensus::Module<T>>::set_code(new)?;
			Self::deposit_event(RawEvent::Upgraded);
		}

		fn set_key(origin, new: <T::Lookup as StaticLookup>::Source) {
			// This is a public call, so we ensure that the origin is some signed account.
			let _sender = ensure_signed(origin)?;
			ensure!(_sender == Self::key(), "only the current upgrade key can use the upgrade_key module");
			let new = T::Lookup::lookup(new)?;

			Self::deposit_event(RawEvent::KeyChanged(Self::key()));
			<Key<T>>::put(new);
		}
	}
}

/// An event in this module.
decl_event!(
	pub enum Event<T> where AccountId = <T as system::Trait>::AccountId {
		/// An upgrade just happened.
		Upgraded,
		/// An upgrade just happened; old key is supplied as an argument.
		KeyChanged(AccountId),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as UpgradeKey {
		Key get(key) config(): T::AccountId;
	}
}
