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

//! # Post Pallet

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
mod benchmarks;
pub mod weights;

use sp_std::prelude::*;
use sp_runtime::{RuntimeDebug, SaturatedConversion, traits::Saturating};

use frame_support::{decl_module, decl_event, decl_storage, decl_error, ensure};
use frame_support::{
	traits::{Currency, ReservableCurrency, Get},
};
use frame_system::ensure_signed;
use codec::{Encode, Decode};
pub use weights::WeightInfo;

pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
	/// Balances
	type Currency: ReservableCurrency<Self::AccountId>;
	/// The minimum deposit that needs to be placed for a post.
	type MinDeposit: Get<BalanceOf<Self>>;
	/// The amount per byte users need to deposit.
	type ByteDeposit: Get<BalanceOf<Self>>;
	/// The max length for a topic.
	type MaxTopicLength: Get<usize>;
	/// The max length for a post.
	type MaxPostLength: Get<usize>;
	/// Weight information for extrinsics in this pallet.
	type WeightInfo: WeightInfo;
}

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, Default)]
pub struct Post<Balance, BlockNumber> {
	pub deposit: Balance,
	pub block_number: BlockNumber,
	pub post: Vec<u8>,
}

#[derive(Encode, Decode, Clone, Copy, PartialEq, Eq, RuntimeDebug)]
pub enum PostType {
	Blog,
	Thread,
}

pub type Topic = Vec<u8>;

pub type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

decl_event!(
	pub enum Event<T> where AccountId = <T as frame_system::Trait>::AccountId {
		PostCreated(AccountId, Topic, PostType),
		PostDeleted(AccountId, Topic, PostType),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as Comment {
		/// Blogs: User -> Topic -> Message
		Blog get(fn blog): double_map hasher(twox_64_concat) T::AccountId, hasher(blake2_128_concat) Topic
			=> Option<Post<BalanceOf<T>, T::BlockNumber>>;

		/// Threads: Topic -> User -> Message
		Thread get(fn thread): double_map hasher(blake2_128_concat) Topic, hasher(twox_64_concat) T::AccountId
			=> Option<Post<BalanceOf<T>, T::BlockNumber>>;
	}
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// The comment you are looking for does not exist.
		NotFound,
		/// The topic is too long.
		TopicLength,
		/// The post is too long.
		PostLength,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		#[weight = T::WeightInfo::post()]
		fn post(origin, post_type: PostType, topic: Topic, post: Vec<u8>) {
			let poster = ensure_signed(origin)?;

			let topic_len = topic.len();
			ensure!(topic_len <= T::MaxTopicLength::get(), Error::<T>::TopicLength);
			let post_len = post.len();
			ensure!(post_len <= T::MaxPostLength::get(), Error::<T>::PostLength);

			// Deposit is at least MinDeposit, or grows with topic and post length.
			let deposit = T::ByteDeposit::get().saturating_mul(
				topic_len.saturating_add(post_len).saturated_into()
			).max(T::MinDeposit::get());

			if let Some(post) = match post_type {
				PostType::Blog => Blog::<T>::get(&poster, &topic),
				PostType::Thread => Thread::<T>::get(&topic, &poster),
			} {
				// User already has placed a deposit, we only reserve what we need to.
				let existing_deposit = post.deposit;
				if existing_deposit < deposit {
					T::Currency::reserve(&poster, deposit - existing_deposit)?;
				} else if existing_deposit > deposit {
					T::Currency::unreserve(&poster, existing_deposit - deposit);
				}
			} else {
				// No existing deposit to worry about
				T::Currency::reserve(&poster, deposit)?;
			}

			let block_number = frame_system::Module::<T>::block_number();

			let post = Post {
				deposit,
				block_number,
				post,
			};

			match post_type {
				PostType::Blog => Blog::<T>::insert(&poster, &topic, post),
				PostType::Thread => Thread::<T>::insert(&topic, &poster, post),
			}

			Self::deposit_event(RawEvent::PostCreated(poster, topic, post_type));
		}

		#[weight = T::WeightInfo::delete()]
		fn delete(origin, post_type: PostType, topic: Topic) {
			let poster = ensure_signed(origin)?;

			let post = match post_type {
				PostType::Blog => Blog::<T>::take(&poster, &topic).ok_or(Error::<T>::NotFound)?,
				PostType::Thread => Thread::<T>::take(&topic, &poster).ok_or(Error::<T>::NotFound)?,
			};

			T::Currency::unreserve(&poster, post.deposit);
			Self::deposit_event(RawEvent::PostDeleted(poster, topic, post_type));
		}
	}
}
