// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Sudo Module
//!
//! - [`sudo::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//!
//! ## Overview
//!
//! The Sudo module allows for a single account (called the "sudo key")
//! to execute dispatchable functions that require a `Root` call
//! or designate a new account to replace them as the sudo key.
//! Only one account can be the sudo key at a time.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! Only the sudo key can call the dispatchable functions from the Sudo module.
//!
//! * `sudo` - Make a `Root` call to a dispatchable function.
//! * `set_key` - Assign a new account to be the sudo key.
//!
//! ## Usage
//!
//! ### Executing Privileged Functions
//!
//! The Sudo module itself is not intended to be used within other modules.
//! Instead, you can build "privileged functions" (i.e. functions that require `Root` origin) in other modules.
//! You can execute these privileged functions by calling `sudo` with the sudo key account.
//! Privileged functions cannot be directly executed via an extrinsic.
//!
//! Learn more about privileged functions and `Root` origin in the [`Origin`] type documentation.
//!
//! ### Simple Code Snippet
//!
//! This is an example of a module that exposes a privileged function:
//!
//! ```
//! use frame_support::{decl_module, dispatch};
//! use frame_system::ensure_root;
//!
//! pub trait Trait: frame_system::Trait {}
//!
//! decl_module! {
//!     pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//! 		#[weight = 0]
//!         pub fn privileged_function(origin) -> dispatch::DispatchResult {
//!             ensure_root(origin)?;
//!
//!             // do something...
//!
//!             Ok(())
//!         }
//!     }
//! }
//! # fn main() {}
//! ```
//!
//! ## Genesis Config
//!
//! The Sudo module depends on the [`GenesisConfig`](./struct.GenesisConfig.html).
//! You need to set an initial superuser account as the sudo `key`.
//!
//! ## Related Modules
//!
//! * [Democracy](../pallet_democracy/index.html)
//!
//! [`Call`]: ./enum.Call.html
//! [`Trait`]: ./trait.Trait.html
//! [`Origin`]: https://docs.substrate.dev/docs/substrate-types

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use sp_runtime::{DispatchResult, traits::StaticLookup};

use frame_support::{
	Parameter, decl_module, decl_event, decl_storage, decl_error, ensure,
};
use frame_support::{
	weights::{Weight, GetDispatchInfo, Pays},
	traits::{UnfilteredDispatchable, Get},
	dispatch::DispatchResultWithPostInfo,
};
use frame_system::ensure_signed;

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// A sudo-able call.
	type Call: Parameter + UnfilteredDispatchable<Origin=Self::Origin> + GetDispatchInfo;
}

decl_module! {
	/// Sudo module declaration.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		/// Authenticates the sudo key and dispatches a function call with `Root` origin.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// # <weight>
		/// - O(1).
		/// - Limited storage reads.
		/// - One DB write (event).
		/// - Weight of derivative `call` execution + 10,000.
		/// # </weight>
		#[weight = (call.get_dispatch_info().weight + 10_000, call.get_dispatch_info().class)]
		fn sudo(origin, call: Box<<T as Trait>::Call>) -> DispatchResultWithPostInfo {
			// This is a public call, so we ensure that the origin is some signed account.
			let sender = ensure_signed(origin)?;
			ensure!(sender == Self::key(), Error::<T>::RequireSudo);

			let res = call.dispatch_bypass_filter(frame_system::RawOrigin::Root.into());
			Self::deposit_event(RawEvent::Sudid(res.map(|_| ()).map_err(|e| e.error)));
			// Sudo user does not pay a fee.
			Ok(Pays::No.into())
		}

		/// Authenticates the sudo key and dispatches a function call with `Root` origin.
		/// This function does not check the weight of the call, and instead allows the
		/// Sudo user to specify the weight of the call.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// # <weight>
		/// - O(1).
		/// - The weight of this call is defined by the caller.
		/// # </weight>
		#[weight = (*_weight, call.get_dispatch_info().class)]
		fn sudo_unchecked_weight(origin, call: Box<<T as Trait>::Call>, _weight: Weight) -> DispatchResultWithPostInfo {
			// This is a public call, so we ensure that the origin is some signed account.
			let sender = ensure_signed(origin)?;
			ensure!(sender == Self::key(), Error::<T>::RequireSudo);

			let res = call.dispatch_bypass_filter(frame_system::RawOrigin::Root.into());
			Self::deposit_event(RawEvent::Sudid(res.map(|_| ()).map_err(|e| e.error)));
			// Sudo user does not pay a fee.
			Ok(Pays::No.into())
		}

		/// Authenticates the current sudo key and sets the given AccountId (`new`) as the new sudo key.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// # <weight>
		/// - O(1).
		/// - Limited storage reads.
		/// - One DB change.
		/// # </weight>
		#[weight = 0]
		fn set_key(origin, new: <T::Lookup as StaticLookup>::Source) -> DispatchResultWithPostInfo {
			// This is a public call, so we ensure that the origin is some signed account.
			let sender = ensure_signed(origin)?;
			ensure!(sender == Self::key(), Error::<T>::RequireSudo);
			let new = T::Lookup::lookup(new)?;

			Self::deposit_event(RawEvent::KeyChanged(Self::key()));
			<Key<T>>::put(new);
			// Sudo user does not pay a fee.
			Ok(Pays::No.into())
		}

		/// Authenticates the sudo key and dispatches a function call with `Signed` origin from
		/// a given account.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// # <weight>
		/// - O(1).
		/// - Limited storage reads.
		/// - One DB write (event).
		/// - Weight of derivative `call` execution + 10,000.
		/// # </weight>
		#[weight = (
			call.get_dispatch_info().weight
				.saturating_add(10_000)
				 // AccountData for inner call origin accountdata.
				.saturating_add(T::DbWeight::get().reads_writes(1, 1)),
			call.get_dispatch_info().class
		)]
		fn sudo_as(origin,
			who: <T::Lookup as StaticLookup>::Source,
			call: Box<<T as Trait>::Call>
		) -> DispatchResultWithPostInfo {
			// This is a public call, so we ensure that the origin is some signed account.
			let sender = ensure_signed(origin)?;
			ensure!(sender == Self::key(), Error::<T>::RequireSudo);

			let who = T::Lookup::lookup(who)?;

			let res = match call.dispatch_bypass_filter(frame_system::RawOrigin::Signed(who).into()) {
				Ok(_) => true,
				Err(e) => {
					sp_runtime::print(e);
					false
				}
			};

			Self::deposit_event(RawEvent::SudoAsDone(res));
			// Sudo user does not pay a fee.
			Ok(Pays::No.into())
		}
	}
}

decl_event!(
	pub enum Event<T> where AccountId = <T as frame_system::Trait>::AccountId {
		/// A sudo just took place. \[result\]
		Sudid(DispatchResult),
		/// The \[sudoer\] just switched identity; the old key is supplied.
		KeyChanged(AccountId),
		/// A sudo just took place. \[result\]
		SudoAsDone(bool),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as Sudo {
		/// The `AccountId` of the sudo key.
		Key get(fn key) config(): T::AccountId;
	}
}

decl_error! {
	/// Error for the Sudo module
	pub enum Error for Module<T: Trait> {
		/// Sender must be the Sudo account
		RequireSudo,
	}
}
