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

//! # Sudo Module
//!
//! ## Overview
//! 
//! The sudo module allows for a single account to be set as the sudo key of your blockchain. The sudo key can execute dispatchable functions which require a `Root` call or assign a new account to replace them as the sudo key.
//! 
//! You can start using the Sudo module by implementing the sudo [`Trait`].
//! 
//! Supported dispatchables functions are documented as part of the [`Call`] enum.
//! 
//! ## Interface
//! 
//! ### Dispatchable
//! 
//! Only the sudo key can call the dispatchable functions from the Sudo module.
//! 
//! * `sudo` - Make a `Root` call to a dispatchable function.
//! * `set_key` - Assign a new account to be the key of the superuser
//! 
//! Please refer to the [`Call`] enum and its associated variants for a detailed list of dispatchable functions.
//!
//! ## Usage
//! 
//! ### Prerequisites
//! 
//! To use the sudo module in your runtime, you must implement the following trait in your runtime:
//! 
//! ```
//! impl sudo::Trait for Runtime {
//! 	/// The uniquitous event type.
//! 	type Event = Event;
//! 	type Proposal = Call;
//! }
//! ```
//! 
//! You can then import the sudo module in your `construct_runtime!` macro with:
//! 
//! ```
//! Sudo: sudo,
//! ```
//! 
//! ### Simple Code Snippet
//! 
//! The Sudo module itself is not intended to be used within other modules. However, you can build other dispatchable functions to take advantage of this sudo module by requiring the function only accept calls from `Root`.
//! 
//! For example:
//! 
//! ```rust,ignore
//! use support::{decl_module, dispatch::Result};
//! use system::ensure_root;
//! 
//! pub trait Trait: system::Trait {}
//! 
//! decl_module! {
//!     pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//!         pub fn privileged_function(origin) -> Result {
//!             ensure_root(origin)?;
//!             
//!             // do something...
//! 
//!             Ok(())
//!         }
//!     }
//! }
//! ```
//! 
//! This `privileged_function()` can not directly be executed via an extrinsic, but can be called via `sudo()` function.
//! 
//! 
//! ### Example from SRML
//! 
//! The consensus module exposes a `set_code()` function which requires a `Root` call and allows you to set the on-chain Wasm runtime code:
//! 
//! ```
//! /// Set the new code.
//! pub fn set_code(new: Vec<u8>) {
//!     storage::unhashed::put_raw(well_known_keys::CODE, &new);
//! }
//! ```
//! 
//! Note that this function does not include the `origin` parameter, so the `decl_module` macro adds `origin` and the `ensure_root` check automatically.
//! 
//! ## Genesis Config
//! 
//! To use the sudo module, you need to include an initial superuser account to be set as the sudo `key`.
//! 
//! ```
//! GenesisConfig {
//!     sudo: Some(SudoConfig {
//!         key: AccountId,
//!     })
//! }
//! ```
//! 
//! ## Related Modules
//! 
//! * Consensus
//! * Democracy
//! 
//! ## References

#![cfg_attr(not(feature = "std"), no_std)]

use sr_std::prelude::*;
use sr_primitives::traits::StaticLookup;
use srml_support::{StorageValue, Parameter, Dispatchable, decl_module, decl_event, decl_storage, ensure};
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

		/// Allow the sudo key to make a `Root` call to a dispatchable function
		///
		/// The dispatch origin for this call must be _Signed_.
		fn sudo(origin, proposal: Box<T::Proposal>) {
			// This is a public call, so we ensure that the origin is some signed account.
			let sender = ensure_signed(origin)?;
			ensure!(sender == Self::key(), "only the current sudo key can sudo");

			let ok = proposal.dispatch(system::RawOrigin::Root.into()).is_ok();
			Self::deposit_event(RawEvent::Sudid(ok));
		}

		/// Allow the current sudo key to set an AccountId as the new sudo key
		///
		/// The dispatch origin for this call must be _Signed_.
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
		/// The AccountId of the sudo key
		Key get(key) config(): T::AccountId;
	}
}
