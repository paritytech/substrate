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

//! A lottery pallet that uses participation in the network to purchase tickets.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
mod benchmarking;
mod weights;

use sp_std::prelude::*;
use sp_runtime::{DispatchError, ModuleId};
use sp_runtime::traits::{AccountIdConversion, Saturating, Zero};
use frame_support::{Parameter, decl_module, decl_error, decl_event, decl_storage, ensure, RuntimeDebug};
use frame_support::dispatch::{Dispatchable, DispatchResult, GetDispatchInfo};
use frame_support::traits::{
	Currency, ReservableCurrency, Get, EnsureOrigin, ExistenceRequirement::KeepAlive, Randomness,
};
use frame_support::weights::Weight;
use frame_system::ensure_signed;
use codec::{Encode, Decode};
pub use weights::WeightInfo;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

/// The module's config trait.
pub trait Trait: frame_system::Trait {
	/// The Lottery's module id
	type ModuleId: Get<ModuleId>;

	/// A dispatchable call.
	type Call: Parameter + Dispatchable<Origin=Self::Origin> + GetDispatchInfo + From<frame_system::Call<Self>>;

	/// The currency trait.
	type Currency: ReservableCurrency<Self::AccountId>;

	/// Something that provides randomness in the runtime.
	type Randomness: Randomness<Self::Hash>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// The manager origin.
	type ManagerOrigin: EnsureOrigin<Self::Origin>;

	/// The max number of calls available in a single lottery.
	type MaxCalls: Get<usize>;

	/// Weight information for extrinsics in this pallet.
	type WeightInfo: WeightInfo;
}

type Index = u32;

// Any runtime call can be encoded into two bytes which represent the pallet and call index.
// We use this to uniquely match someone's incoming call with the calls configured for the lottery.
type CallIndex = (u8, u8);

decl_storage! {
	trait Store for Module<T: Trait> as Lottery {
		/// The configuration for the current lottery.
		Lottery: Option<LotteryConfig<T::BlockNumber, BalanceOf<T>>>;
		/// Users who have purchased a ticket.
		Participants: map hasher(twox_64_concat) T::AccountId => Vec<CallIndex>;
		/// Total number of tickets sold.
		TicketsCount: Index;
		/// Each ticket's owner.
		Tickets: map hasher(twox_64_concat) Index => Option<T::AccountId>;
	}
}

decl_event!(
	pub enum Event<T> where
		<T as frame_system::Trait>::AccountId,
		Balance = BalanceOf<T>,
		Call = <T as Trait>::Call,
	{
		/// A lottery has been started!
		LotteryStarted,
		/// A winner has been chosen!
		Winner(AccountId, Balance),
		/// A ticket has been bought!
		TicketBought(AccountId, Call),
	}
);

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// An overflow has occurred.
		Overflow,
		/// A lottery has not been configured.
		NotConfigured,
		/// A lottery has not started.
		NotStarted,
		/// A lottery is already in progress.
		InProgress,
		/// A lottery has already ended.
		AlreadyEnded,
		/// The call is not valid for an open lottery.
		InvalidCall,
		/// You are already participating in the lottery with this call.
		AlreadyParticipating,
		/// Too many calls for a single lottery.
		TooManyCalls,
		/// Failed to encode calls
		EncodingFailed,
	}
}

#[derive(Encode, Decode, Default, RuntimeDebug)]
pub struct LotteryConfig<BlockNumber, Balance> {
	/// Price per entry.
	price: Balance,
	/// Starting block of the lottery.
	start: BlockNumber,
	/// Ending block of the lottery.
	end: BlockNumber,
	/// Payout block of the lottery.
	payout: BlockNumber,
	/// Calls available this lottery.
	calls: Vec<CallIndex>,
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin, system = frame_system {
		/// TODO: Expose Constants

		fn deposit_event() = default;

		#[weight = 0]
		fn setup_lottery(
			origin,
			price: BalanceOf<T>,
			start: T::BlockNumber,
			end: T::BlockNumber,
			payout: T::BlockNumber,
			calls: Vec<<T as Trait>::Call>,
		) {
			T::ManagerOrigin::ensure_origin(origin)?;
			ensure!(calls.len() <= T::MaxCalls::get(), Error::<T>::TooManyCalls);
			let indices = Self::calls_to_indices(&calls)?;
			Lottery::<T>::try_mutate(|lottery| -> DispatchResult {
				ensure!(lottery.is_none(), Error::<T>::InProgress);
				*lottery = Some(LotteryConfig { price, start, end, payout, calls: indices });
				Ok(())
			})?;
			Self::deposit_event(RawEvent::LotteryStarted);
		}

		#[weight = 0]
		fn buy_ticket(origin, call: <T as Trait>::Call) {
			let caller = ensure_signed(origin.clone())?;
			call.clone().dispatch(origin).map_err(|e| e.error)?;

			// Only try to buy a ticket if the underlying call is successful.
			// Not much we can do if this fails.
			let _ = Self::do_buy_ticket(&caller, &call);
		}

		fn on_initialize(n: T::BlockNumber) -> Weight {
			if Lottery::<T>::get().map_or(false, |config| config.payout <= n) {
				let (lottery_account, lottery_balance) = Self::pot();
				let ticket_count = TicketsCount::get();

				let winning_number = Self::choose_winner(ticket_count);
				let winner = Tickets::<T>::get(winning_number).unwrap_or(lottery_account);
				// Not much we can do if this fails...
				let _ = T::Currency::transfer(&Self::account_id(), &winner, lottery_balance, KeepAlive);

				Self::deposit_event(RawEvent::Winner(winner, lottery_balance));

				Lottery::<T>::kill();
				TicketsCount::kill();
				Participants::<T>::remove_all();
				Tickets::<T>::remove_all();

				return T::DbWeight::get().reads_writes(2, ticket_count.saturating_mul(2).into())
			} else {
				return Weight::zero()
			}
		}

	}
}

impl<T: Trait> Module<T> {
	/// The account ID of the lottery pot.
	///
	/// This actually does computation. If you need to keep using it, then make sure you cache the
	/// value and only call this once.
	pub fn account_id() -> T::AccountId {
		T::ModuleId::get().into_account()
	}

	/// Return the pot account and amount of money in the pot.
	// The existential deposit is not part of the pot so lottery account never gets deleted.
	fn pot() -> (T::AccountId, BalanceOf<T>) {
		let account_id = Self::account_id();
		let balance = T::Currency::free_balance(&account_id)
			.saturating_sub(T::Currency::minimum_balance());

		(account_id, balance)
	}

	// Converts a vector of calls into a vector of call indices.
	fn calls_to_indices(calls: &[<T as Trait>::Call]) -> Result<Vec<CallIndex>, DispatchError> {
		let mut indices = Vec::with_capacity(calls.len());
		for c in calls.iter() {
			let index = Self::call_to_index(c)?;
			indices.push(index)
		}
		Ok(indices)
	}

	// Convert a call to it's call index by encoding the call and taking the first two bytes.
	fn call_to_index(call: &<T as Trait>::Call) -> Result<CallIndex, DispatchError> {
		let encoded_call = call.encode();
		if encoded_call.len() < 2 { Err(Error::<T>::EncodingFailed)? }
		return Ok((encoded_call[0], encoded_call[1]))
	}

	// Logic for buying a ticket.
	fn do_buy_ticket(caller: &T::AccountId, call: &<T as Trait>::Call) -> DispatchResult {
		// Check the call is valid lottery
		let config = Lottery::<T>::get().ok_or(Error::<T>::NotConfigured)?;
		let block_number = frame_system::Module::<T>::block_number();
		ensure!(block_number >= config.start, Error::<T>::NotStarted);
		ensure!(block_number < config.end, Error::<T>::AlreadyEnded);
		let call_index = Self::call_to_index(call)?;
		ensure!(config.calls.iter().any(|c| call_index == *c), Error::<T>::InvalidCall);
		let ticket_count = TicketsCount::get();
		let new_ticket_count = ticket_count.checked_add(1).ok_or(Error::<T>::Overflow)?;
		// Try to update the participant status
		Participants::<T>::try_mutate(&caller, |participating_calls| -> DispatchResult {
			// Check that user is not already participating under this call.
			ensure!(!participating_calls.iter().any(|c| call_index == *c), Error::<T>::AlreadyParticipating);
			// Check user has enough funds and send it to the Lottery account.
			T::Currency::transfer(caller, &Self::account_id(), config.price, KeepAlive)?;
			// Create a new ticket.
			TicketsCount::put(new_ticket_count);
			Tickets::<T>::insert(ticket_count, caller.clone());
			participating_calls.push(call_index);
			Ok(())
		})?;

		Self::deposit_event(RawEvent::TicketBought(caller.clone(), call.clone()));

		Ok(())
	}

	// Randomly choose a winner from among the total number of participants.
	fn choose_winner(total: u32) -> u32 {
		let random_seed = T::Randomness::random(b"lottery");
		let random_number = <u32>::decode(&mut random_seed.as_ref())
			.expect("secure hashes should always be bigger than u32; qed");
		random_number % total
	}
}
