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

//! # Comment Pallet

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use sp_runtime::{DispatchResult, traits::StaticLookup};

use frame_support::{
	Parameter, decl_module, decl_event, decl_storage, decl_error, ensure,
};
use frame_support::{
	weights::{Weight, GetDispatchInfo, Pays},
	traits::UnfilteredDispatchable,
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

	type Currency: ReservableCurrency<Self::AccountId>;

	type ByteDeposit: Get<BalanceOf<Self>>;

	type BaseTax: Get<BalanceOf<Self>>;

	type ByteTax: Get<BalanceOf<Self>>;

	type MaxKeyLength: Get<usize>;

	type MaxCommentLength: Get<usize>;

	type MinDeposit: Get<BalanceOf<Self>>;

	type BurnDestination: Get<Self::Origin>;
}

struct Comment<Balance, BlockNumber> {
	pub deposit: Balance,
	pub block_number: BlockNumber,
	pub comment: Vec<u8>,
}

struct Tax<Balance> {
	pub base: Balance,
	pub per_byte: Balance,
}

decl_event!(
	pub enum Event<T> where AccountId = <T as frame_system::Trait>::AccountId {
		CommentCreated(AccountId, Vec);
		CommentRemoved(AccountId, Key);
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as Sudo {
		/// The `AccountId` of the sudo key.
		Comments fn(comments): double_map hasher(twox_64_concat) T::AccountId, hasher(blake2_128_concat) Vec<u8>
			=> Option<Comment<BalanceOf<T>, T::BlockNumber>>;

		/// The tax rate per byte for data stored on chain.
		Taxes get(fn taxes) config(): Tax<BalanceOf<T>>;
	}
}

decl_error! {
	/// Error for the Sudo module
	pub enum Error for Module<T: Trait> {
		KeyTooLarge,
		ValueTooLarge,
		NotFound,
		CannotRemove,
	}
}

decl_module! {
	/// Sudo module declaration.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		#[weight = 0]
		fn comment(origin, key: Vec<u8>, value: Vec<u8>, extra_deposit: BalanceOf<T>) {
			let sender = ensure_signed(origin)?;

			let key_len = key.len();
			ensure(key_len <= T::MaxKeyLength::get(), Error::<T>::KeyTooLarge);
			let value_len = value.len();
			ensure(key_len <= T::MaxKeyLength::get(), Error::<T>::ValueTooLarge);

			let deposit = T::ByteFee::get().saturating_mul(key_len.saturating_add(value_len));
			T::Currency::reserve(sender, deposit)?;

			let block_number = frame_system::Module::<T>::block_number();
			let tax_rate = Self::tax();
			let comment = Comment {
				deposit,
				block_number,
				tax_rate,
				comment: value,
			};
			Comments::<T>::insert(sender, key, comment);

			Self::deposit_event(RawEvent::CommentCreated(sender, key))
		}

		#[weight = 0]
		fn remove_comment(origin, who: T::AccountId, key: Vec<u8>) {
			let sender = ensure_signed(origin)?;

			let key_len = key.len();
			ensure(key_len <= T::MaxKeyLength::get(), Error::<T>::KeyTooLarge);

			let { deposit, block_number, comment } = Self::comments(&who, &key).unwrap_or(Error::<T>::NotFound)?;
			let taxes = Self::taxes();

			let tax = (taxes.base.saturating_add(taxes.per_byte.saturating_mul(comment.len())))
				.saturating_mul(block_number);
			let remaining_deposit = deposit.saturating_sub(tax);

			let can_be_removed = remaining_deposit <= T::MinDeposit::get() || sender == who;
			ensure!(can_be_removed, Error::<T>::CannotRemove);

			// Comment will be removed. Actions are always the same.
			T::Currency::repatriate_reserved(who, sender, remaining_deposit, Status::Free);
			T::Currency::repatriate_reserved(who, T::BurnDestination::get(), tax, Status::Free);
			Comments::<T>::remove(who, key);
			Self::deposit_event(RawEvent::CommentRemoved(who, key));
		}

		#[weight = 0]
		fn increase_deposit(origin, who: T::AccountId, key: Vec<u8>, extra_deposit: BalanceOf<T>) {
			let sender = ensure_signed(origin)?

			let key_len = key.len();
			ensure(key_len <= T::MaxKeyLength::get(), Error::<T>::KeyTooLarge);

			Comments::<T>::try_mutate(who, key, |mut comment| {
				T::Currency::transfer(sender, who, )
			});
		}
	}
}
