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

extern crate sr_std;
#[cfg(test)]
extern crate sr_io;
#[cfg(test)]
extern crate substrate_primitives;
extern crate sr_primitives;
#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate parity_codec_derive;
extern crate parity_codec as codec;
#[macro_use]
extern crate srml_support as support;
extern crate srml_system as system;
extern crate srml_consensus as consensus;

use sr_std::prelude::*;
use support::{StorageValue, dispatch::Result};
use system::ensure_signed;

pub trait Trait: consensus::Trait + system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

decl_module! {
	// Simple declaration of the `Module` type. Lets the macro know what its working on.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;
		fn upgrade(origin, new: Vec<u8>) -> Result {
			// This is a public call, so we ensure that the origin is some signed account.
			let _sender = ensure_signed(origin)?;
			ensure!(_sender == Self::key(), "only the current upgrade key can use the upgrade_key module");

			<consensus::Module<T>>::set_code(new)?;
			Self::deposit_event(RawEvent::Upgraded);

			Ok(())
		}

		fn set_key(origin, new: T::AccountId) -> Result {
			// This is a public call, so we ensure that the origin is some signed account.
			let _sender = ensure_signed(origin)?;
			ensure!(_sender == Self::key(), "only the current upgrade key can use the upgrade_key module");

			Self::deposit_event(RawEvent::KeyChanged(Self::key()));
			<Key<T>>::put(new);

			Ok(())
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
