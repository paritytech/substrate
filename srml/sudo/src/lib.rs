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
#[macro_use]
extern crate parity_codec_derive;
extern crate parity_codec as codec;
#[macro_use]
extern crate srml_support as support;

extern crate srml_system as system;

use sr_std::prelude::*;
use sr_primitives::traits::StaticLookup;
use support::{StorageValue, Parameter, Dispatchable};
use system::ensure_signed;

pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// A sudo-able call.
	type Proposal: Parameter + Dispatchable<Origin=Self::Origin>;
}

decl_module! {
	// Simple declaration of the `Module` type. Lets the macro know what its working on.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		fn sudo(origin, proposal: Box<T::Proposal>) {
			// This is a public call, so we ensure that the origin is some signed account.
			let sender = ensure_signed(origin)?;
			ensure!(sender == Self::key(), "only the current sudo key can sudo");

			let ok = proposal.dispatch(system::RawOrigin::Root.into()).is_ok();
			Self::deposit_event(RawEvent::Sudid(ok));
		}

		fn set_key(origin, new: <T::Lookup as StaticLookup>::Source) {
			// This is a public call, so we ensure that the origin is some signed account.
			let sender = ensure_signed(origin)?;
			ensure!(sender == Self::key(), "only the current sudo key can change the sudo key");
			let new = T::Lookup::lookup(new)?;

			Self::deposit_event(RawEvent::KeyChanged(Self::key()));
			<Key<T>>::put(new);
		}
	}
}

/// An event in this module.
decl_event!(
	pub enum Event<T> where AccountId = <T as system::Trait>::AccountId {
		/// A sudo just took place.
		Sudid(bool),
		/// The sudoer just switched identity; the old key is supplied.
		KeyChanged(AccountId),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as Sudo {
		Key get(key) config(): T::AccountId;
	}
}
