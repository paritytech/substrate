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

//! EVM execution module for Substrate

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use rstd::collections::btree_map::BTreeMap as Map;
use support::{decl_module, decl_storage, decl_event};
#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use codec::{Encode, Decode};
use primitives::{U256, H256, H160};

/// EVM module trait
pub trait Trait: balances::Trait {
	/// The overarching event type.
	type Event: From<Event> + Into<<Self as system::Trait>::Event>;
}

#[derive(Clone, Eq, PartialEq, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct ExternalAccount {
	pub nonce: U256,
	pub balance: U256,
}

#[derive(Clone, Eq, PartialEq, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Contract {
	pub nonce: U256,
	pub balance: U256,
	pub code: Vec<u8>,
	pub storage: Map<H256, H256>,
}

#[derive(Clone, Eq, PartialEq, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Log {
	pub address: H160,
	pub topcis: Vec<H256>,
	pub data: Vec<u8>,
}

decl_storage! {
	trait Store for Module<T: Trait> as Example {
		ExternalAccounts get(fn external_accounts) config(): map T::AccountId => ExternalAccount;
		Contracts get(fn contracts) config(): map H160 => Contract;
	}
}

decl_event!(
	/// EVM events
	pub enum Event {
		/// Ethereum events from contracts.
		Log(Log),
	}
);

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;
	}
}

impl<T: Trait> Module<T> {

}
