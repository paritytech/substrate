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
use sp_runtime::{
	DispatchResult, RuntimeDebug, SaturatedConversion,
	traits::{Saturating},
};

use frame_support::{decl_module, decl_event, decl_storage, decl_error, ensure};
use frame_support::{
	traits::{Currency, ReservableCurrency, Get},
};
use frame_system::ensure_signed;
use codec::{Encode, Decode};

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
	/// Balances
	type Currency: ReservableCurrency<Self::AccountId>;
	/// The minimum deposit that needs to be placed for a comment.
	type MinDeposit: Get<BalanceOf<Self>>;
	/// The amount per byte users need to deposit.
	type ByteDeposit: Get<BalanceOf<Self>>;
	/// The maximum number of bytes for a topic.
	type MaxTopicLength: Get<usize>;
	/// The maximum number of bytes for a comment.
	type MaxCommentLength: Get<usize>;
}

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, Default)]
pub struct Post<Balance, BlockNumber> {
	pub deposit: Balance,
	pub block_number: BlockNumber,
	pub comment: Vec<u8>,
}

#[derive(Encode, Decode, Clone, Copy, PartialEq, Eq, RuntimeDebug)]
pub enum PostType {
	Blog,
	Thread,
}

pub type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

decl_event!(
	pub enum Event<T> where AccountId = <T as frame_system::Trait>::AccountId {
		CommentPosted(AccountId, Vec<u8>),
		CommentDeleted(AccountId, Vec<u8>),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as Comment {
		/// Blogs: User -> Topic -> Message
		Blog get(fn blog): double_map hasher(twox_64_concat) T::AccountId, hasher(blake2_128_concat) Vec<u8>
			=> Option<Post<BalanceOf<T>, T::BlockNumber>>;

		/// Threads: Topic -> User -> Message
		Thread get(fn thread): double_map hasher(blake2_128_concat) Vec<u8>, hasher(twox_64_concat) T::AccountId
			=> Option<Post<BalanceOf<T>, T::BlockNumber>>;
	}
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// The topic provided is larger than allowed.
		TopicTooLarge,
		/// The topic provided is larger than allowed.
		CommentTooLarge,
		/// The comment you are looking for does not exist.
		NotFound,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		#[weight = 0]
		fn post(origin, topic: Vec<u8>, comment: Vec<u8>, post_type: PostType) {
			let poster = ensure_signed(origin)?;
			Self::impl_post(&poster, &topic, comment, post_type)?;
		}

		#[weight = 0]
		fn delete(origin, topic: Vec<u8>, post_type: PostType) {
			let poster = ensure_signed(origin)?;
			Self::impl_delete(&poster, &topic, post_type)?;
		}
	}
}

impl<T: Trait> Module<T> {
	fn impl_post(who: &T::AccountId, topic: &[u8], comment: Vec<u8>, post_type: PostType) -> DispatchResult {
			let topic_len = topic.len();
			ensure!(topic_len <= T::MaxTopicLength::get(), Error::<T>::TopicTooLarge);
			let comment_len = comment.len();
			ensure!(comment_len <= T::MaxCommentLength::get(), Error::<T>::CommentTooLarge);

			let deposit = T::ByteDeposit::get().saturating_mul(
				topic_len.saturating_add(comment_len).saturated_into()
			);
			T::Currency::reserve(who, deposit.max(T::MinDeposit::get()))?;

			let block_number = frame_system::Module::<T>::block_number();

			let post = Post {
				deposit,
				block_number,
				comment,
			};

			match post_type {
				PostType::Blog => Blog::<T>::insert(who, topic, post),
				PostType::Thread => Thread::<T>::insert(topic, who, post),
			}

			Ok(())
	}

	fn impl_delete(who: &T::AccountId, topic: &[u8], post_type: PostType) -> DispatchResult {
		let topic_len = topic.len();
		ensure!(topic_len <= T::MaxTopicLength::get(), Error::<T>::TopicTooLarge);

		let post = match post_type {
			PostType::Blog => Blog::<T>::take(who, topic).ok_or(Error::<T>::NotFound)?,
			PostType::Thread => Thread::<T>::take(topic, who).ok_or(Error::<T>::NotFound)?,
		};

		T::Currency::unreserve(who, post.deposit);
		Ok(())
		//Self::deposit_event(RawEvent::CommentDeleted(who, topic));
	}
}
