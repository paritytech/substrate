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
use sp_runtime::RuntimeDebug;
use sp_arithmetic::traits::Zero;
use frame_support::{
	decl_module, decl_storage, decl_event, dispatch::DispatchResult,
	traits::{Get, Currency, ReservableCurrency},
	storage::IterableStorageMap,
};
use frame_system::{self as system, ensure_signed};

mod exec;
mod gas;
mod schedule;

pub use crate::gas::{Gas, Token};
pub use crate::schedule::Schedule;

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
pub type MessageFor<T> = Message<AccountIdFor<T>, BalanceFor<T>, HashFor<T>>;

/// Actor data type from actors pallet's point of view.
pub type ActorInfoFor<T> = ActorInfo<AccountIdFor<T>, BalanceFor<T>, HashFor<T>>;

/// Code hash type.
pub type HashFor<T> = <T as frame_system::Trait>::Hash;

/// Message type that actors send around.
#[derive(Clone, Eq, PartialEq, RuntimeDebug, Encode, Decode)]
pub struct Message<A, B, H> {
	/// Source of the message.
	pub source: A,
	/// Balance encoded in the message.
	pub value: B,
	/// Topics of the message.
	pub topics: Vec<H>,
	/// Data field up to receiver's interpretation.
	pub data: Vec<u8>,
}

/// Actor data as stored on storage.
#[derive(Clone, Eq, PartialEq, RuntimeDebug, Encode, Decode, Default)]
pub struct ActorInfo<A, B, H> {
	/// Code hash of the actor.
	pub code_hash: Option<H>,
	/// Storage values of the actor.
	pub storage: BTreeMap<StorageKey, Vec<u8>>,
	/// Incoming messages to the actor.
	pub messages: Vec<Message<A, B, H>>,
}

/// Trait definition for actors pallet.
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
	/// Currency type.
	type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;
	/// Single process gas limit.
	type ProcessGasLimit: Get<Gas>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Actors {
		/// Current cost schedule for contracts.
		CurrentSchedule get(fn current_schedule) config(): Schedule = Schedule::default();
		/// A mapping from an original code hash to the original code, untouched by instrumentation.
		pub PristineCode: map hasher(identity) HashFor<T> => Option<Vec<u8>>;
		/// A mapping between an original code hash and instrumented wasm code, ready for execution.
		pub CodeStorage: map hasher(identity) HashFor<T> => Option<exec::PrefabWasmModule>;

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
		<T as frame_system::Trait>::AccountId,
		<T as frame_system::Trait>::Hash
	{
		/// A new actor has been deployed, with `AccountId`.
		ActorDeployed(AccountId),

		/// Code with the specified hash has been stored.
		CodeStored(Hash),
	}
);

decl_module! {
	/// Module definition for actors pallet;
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		/// Stores the given binary Wasm code into the chain's storage and returns its `codehash`.
		/// You can instantiate contracts only with stored code.
		#[weight = 0]
		pub fn put_code(
			origin,
			code: Vec<u8>
		) -> DispatchResult {
			ensure_signed(origin)?;
			let schedule = <Module<T>>::current_schedule();
			let result = exec::save_code::<T>(code, &schedule);
			if let Ok(code_hash) = result {
				Self::deposit_event(RawEvent::CodeStored(code_hash));
			}
			result.map(|_| ()).map_err(Into::into)
		}

		/// Send a message to an actor.
		#[weight = 0]
		fn send_message(
			origin,
			target: AccountIdFor<T>,
			value: BalanceFor<T>,
			topics: Vec<HashFor<T>>,
			data: Vec<u8>,
		) -> DispatchResult {
			let source = ensure_signed(origin)?;
			T::Currency::reserve(&source, value)?;

			let message = Message {
				source,
				value,
				topics,
				data,
			};
			Self::store_message(target, message);

			Ok(())
		}

		fn on_finalize() {
			for (account_id, _) in ActorInfoOf::<T>::iter() {
				while Self::process_one(account_id.clone()) { }
			}
		}
	}
}

impl<T: Trait> Module<T> {
	/// Process one message from the target account, returns true if a message is processed, false
	/// otherwise.
	fn process_one(account_id: AccountIdFor<T>) -> bool {
		let schedule = Self::current_schedule();

		let (message, code) = match ActorInfoOf::<T>::mutate(&account_id, |actor| {
			actor.code_hash.clone().and_then(|code_hash| {
				actor.messages.pop().map(|message| {
					(message,
					 exec::load_code::<T>(
						 &code_hash,
						 &schedule
					 ).expect("Code is deployed"))
				})
			})
		}) {
			Some(val) => val,
			None => return false,
		};

		let (imbalance, less) = T::Currency::slash_reserved(&message.source, message.value);
		if less > Zero::zero() {
			panic!("Runtime error: reserved fund is less than expected");
		}
		T::Currency::resolve_creating(&account_id, imbalance);

		let mut context = exec::Context::<T>::new(&schedule, account_id, message.clone());
		match exec::execute(
			&code,
			"process",
			message.encode(),
			&mut context,
			&schedule,
			T::ProcessGasLimit::get()
		) {
			Ok(()) => (),
			Err(()) => return false, // TODO: maybe also distinguish no message and execution failed.
		}

		context.apply();
		true
	}

	/// Store message on destination. If the code is empty, the message should succeed instantly.
	fn store_message(target: AccountIdFor<T>, message: MessageFor<T>) {
		let has_code = ActorInfoOf::<T>::get(&target).code_hash.is_some();

		if has_code {
			ActorInfoOf::<T>::mutate(target, |actor| {
				actor.messages.push(message);
			});
		} else {
			let (imbalance, less) = T::Currency::slash_reserved(&message.source, message.value);
			if less > Zero::zero() {
				panic!("Runtime error: reserved fund is less than expected");
			}
			T::Currency::resolve_creating(&target, imbalance);
		}
	}
}
