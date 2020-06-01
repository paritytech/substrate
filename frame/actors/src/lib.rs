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

//! # Actors Pallet

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Encode, Decode};
use sp_std::prelude::*;
use sp_std::collections::btree_map::BTreeMap;
use sp_core::H256;
use sp_runtime::RuntimeDebug;
use frame_support::{
	decl_module, decl_storage, decl_event, dispatch::DispatchResult,
	traits::{Get, Currency, ReservableCurrency},
};
use frame_system::{self as system, ensure_signed};

mod exec;

pub type StorageKey = [u8; 32];

/// Account ID type from actors pallet's point of view.
pub type AccountIdFor<T> = <T as frame_system::Trait>::AccountId;

/// Balance type from actors pallet's point of view.
pub type BalanceFor<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

/// Positive imbalance type from actors pallet's point of view.
pub type PositiveImbalanceFor<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::PositiveImbalance;

/// Negative imbalance type from actors pallet's point of view.
pub type NegativeImbalanceFor<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::NegativeImbalance;

/// Message type from actors pallet's point of view.
pub type MessageFor<T> = Message<AccountIdFor<T>, BalanceFor<T>>;

/// Actor data type from actors pallet's point of view.
pub type ActorInfoFor<T> = ActorInfo<AccountIdFor<T>, BalanceFor<T>>;

/// Message type that actors send around.
#[derive(Clone, Eq, PartialEq, RuntimeDebug, Encode, Decode)]
pub struct Message<A, B> {
	/// Source of the message.
	pub source: A,
	/// Balance encoded in the message.
	pub value: B,
	/// Data field up to receiver's interpretation.
	pub data: Vec<u8>,
}

/// Actor data as stored on storage.
#[derive(Clone, Eq, PartialEq, RuntimeDebug, Encode, Decode, Default)]
pub struct ActorInfo<A, B> {
	/// Code of the actor.
	pub code: Vec<u8>,
	/// Storage values of the actor.
	pub storage: BTreeMap<StorageKey, Vec<u8>>,
	/// Incoming messages to the actor.
	pub messages: Vec<Message<A, B>>,
}

/// Trait definition for actors pallet.
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
	/// Max value size of storage.
	type MaxValueSize: Get<u32>;
	/// Currency type.
	type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Actors {
		/// Info associated with a given account.
		///
		/// TWOX-NOTE: SAFE since `AccountId` is a secure hash.
		ActorInfoOf: map hasher(twox_64_concat) T::AccountId => ActorInfoFor<T>;
	}
}

decl_event!(
	/// Events are a simple means of reporting specific conditions and
	/// circumstances that have happened that users, Dapps and/or chain explorers would find
	/// interesting and otherwise difficult to detect.
	pub enum Event<T> where
		AccountId = <T as frame_system::Trait>::AccountId
	{
		/// A new actor has been deployed, with `AccountId`.
		ActorDeployed(AccountId),
	}
);

decl_module! {
	/// Module definition for actors pallet;
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		#[weight = 0]
		fn send_message(
			origin,
			target: AccountIdFor<T>,
			value: BalanceFor<T>,
			data: Vec<u8>,
		) -> DispatchResult {
			let source = ensure_signed(origin)?;
			T::Currency::reserve(&source, value)?;

			let message = Message {
				source,
				value,
				data,
			};
			ActorInfoOf::<T>::mutate(target, |actor| {
				actor.messages.push(message);
			});

			Ok(())
		}
	}
}

impl<T: Trait> Module<T> {

}
