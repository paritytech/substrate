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
//! The sudo module allows for a single account (called the "sudo key")
//! to execute dispatchable functions that require a `Root` call
//! or designate a new account to replace them as the sudo key.
//! Only one account can be the sudo key at a time.
//!
//! You can start using the sudo module by implementing the sudo [`Trait`].
//!
//! Supported dispatchable functions are documented in the [`Call`] enum.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! Only the sudo key can call the dispatchable functions from the sudo module.
//!
//! * `sudo` - Make a `Root` call to a dispatchable function.
//! * `set_key` - Assign a new account to be the sudo key.
//!
//! Please refer to the [`Call`] enum and its associated variants for documentation on each function.
//!
//! ## Usage
//!
//! ### Prerequisites
//!
//! To use the sudo module in your runtime, you must implement the following trait in your runtime:
//!
//! ```ignore
//! impl sudo::Trait for Runtime {
//! 	type Event = Event;
//! 	type Proposal = Call;
//! }
//! ```
//!
//! You can then import the Sudo module in your `construct_runtime!` macro with:
//!
//! ```ignore
//! Sudo: sudo,
//! ```
//!
//! ### Executing Privileged Functions
//!
//! The sudo module itself is not intended to be used within other modules.
//! Instead, you can build "privileged functions" in other modules that require `Root` origin.
//! You can execute these privileged functions by calling `sudo` with the sudo key account.
//! Privileged functions cannot be directly executed via an extrinsic.
//!
//! Learn more about privileged functions and `Root` origin in the [`Origin`] type documentation.
//!
//! ### Simple Code Snippet
//!
//! This is an example of a module that exposes a privileged function:
//!
//! ```ignore
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
//! ### Example from SRML
//!
//! The consensus module exposes a `set_code` privileged function
//! that allows you to set the on-chain Wasm runtime code:
//!
//! ```ignore
//! /// Set the new code.
//! pub fn set_code(new: Vec<u8>) {
//!     storage::unhashed::put_raw(well_known_keys::CODE, &new);
//! }
//! ```
//!
//! ## Genesis Config
//!
//! To use the sudo module, you need to set an initial superuser account as the sudo `key`.
//!
//! ```ignore
//! GenesisConfig {
//!     sudo: Some(SudoConfig {
//!         key: AccountId,
//!     })
//! }
//! ```
//!
//! ## Related Modules
//!
//! * [Consensus](../srml_consensus/index.html)
//! * [Democracy](../srml_democracy/index.html)
//!
//! [`Call`]: ./enum.Call.html
//! [`Trait`]: ./trait.Trait.html
//! [`Origin`]: https://docs.substrate.dev/docs/substrate-types

#![cfg_attr(not(feature = "std"), no_std)]

use sr_primitives::traits::StaticLookup;
use sr_std::prelude::*;
use srml_support::{
    decl_event, decl_module, decl_storage, ensure, Dispatchable, Parameter, StorageValue,
};
use system::ensure_signed;

pub trait Trait: system::Trait {
    /// The overarching event type.
    type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

    /// A sudo-able call.
    type Proposal: Parameter + Dispatchable<Origin = Self::Origin>;
}

decl_module! {
    // Simple declaration of the `Module` type. Lets the macro know what it's working on.
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {
        fn deposit_event<T>() = default;

        /// Authenticates the sudo key and dispatches a function call with `Root` origin.
        ///
        /// The dispatch origin for this call must be _Signed_.
        fn sudo(origin, proposal: Box<T::Proposal>) {
            // This is a public call, so we ensure that the origin is some signed account.
            let sender = ensure_signed(origin)?;
            ensure!(sender == Self::key(), "only the current sudo key can sudo");

            let ok = proposal.dispatch(system::RawOrigin::Root.into()).is_ok();
            Self::deposit_event(RawEvent::Sudid(ok));
        }

        /// Authenticates the current sudo key and sets the given AccountId (`new`) as the new sudo key.
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

decl_event!(
    pub enum Event<T>
    where
        AccountId = <T as system::Trait>::AccountId,
    {
        /// A sudo just took place.
        Sudid(bool),
        /// The sudoer just switched identity; the old key is supplied.
        KeyChanged(AccountId),
    }
);

decl_storage! {
    trait Store for Module<T: Trait> as Sudo {
        /// The `AccountId` of the sudo key.
        Key get(key) config(): T::AccountId;
    }
}
