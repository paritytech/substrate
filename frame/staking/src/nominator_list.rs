// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Provide a linked list of nominators, sorted by stake.

use crate::{Config, Nominations, Pallet};
use codec::{Encode, Decode};
use frame_support::{DefaultNoBound, StorageMap, StorageValue};
use sp_runtime::SaturatedConversion;
use sp_std::marker::PhantomData;

// TODOS:
//
// - update `ElectionDataProvider` impl to use the nominator list to count off the top N

type AccountIdOf<T> = <T as frame_system::Config>::AccountId;

impl<T: Config> Pallet<T> {
	/// `Self` accessor for `NominatorList<T>`
	pub fn nominator_list() -> NominatorList<T> {
		crate::NominatorList::<T>::get()
	}
}

/// Linked list of nominstors, sorted by stake.
#[derive(DefaultNoBound, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct NominatorList<T: Config> {
	head: Option<AccountIdOf<T>>,
	tail: Option<AccountIdOf<T>>,
}

impl<T: Config> NominatorList<T> {
	/// Decode the length of this list without actually iterating over it.
	pub fn decode_len() -> Option<usize> {
		crate::NominatorCount::try_get().ok().map(|n| n.saturated_into())
	}

	/// Get the first member of the list.
	pub fn head(&self) -> Option<Node<T>> {
		self.head.as_ref().and_then(|head| crate::NominatorNodes::try_get(head).ok())
	}

	/// Get the last member of the list.
	pub fn tail(&self) -> Option<Node<T>> {
		self.tail.as_ref().and_then(|tail| crate::NominatorNodes::try_get(tail).ok())
	}

	/// Create an iterator over this list.
	pub fn iter(&self) -> Iter<T> {
		Iter { _lifetime: PhantomData, upcoming: self.head() }
	}
}

#[derive(DefaultNoBound, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Node<T: Config> {
	id: AccountIdOf<T>,
	prev: Option<AccountIdOf<T>>,
	next: Option<AccountIdOf<T>>,
}

impl<T: Config> Node<T> {
	/// Get this node's nominations.
	pub fn nominations(&self) -> Option<Nominations<AccountIdOf<T>>> {
		crate::Nominators::<T>::get(self.id.clone())
	}

	/// Get the previous node.
	pub fn prev(&self) -> Option<Node<T>> {
		self.prev.as_ref().and_then(|prev| crate::NominatorNodes::try_get(prev).ok())
	}

	/// Get the next node.
	pub fn next(&self) -> Option<Node<T>> {
		self.next.as_ref().and_then(|next| crate::NominatorNodes::try_get(next).ok())
	}
}

pub struct Iter<'a, T: Config> {
	_lifetime: sp_std::marker::PhantomData<&'a ()>,
	upcoming: Option<Node<T>>,
}

impl<'a, T: Config> Iterator for Iter<'a, T> {
	type Item = Node<T>;

	fn next(&mut self) -> Option<Self::Item> {
		let next = self.upcoming.take();
		if let Some(next) = next.as_ref() {
			self.upcoming = next.next();
		}
		next
	}
}
