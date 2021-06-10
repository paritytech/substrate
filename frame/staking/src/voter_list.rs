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

use crate::{
	slashing::SlashingSpans, AccountIdOf, Config, Nominations, Nominators, Pallet, VotingDataOf,
	VoteWeight,
};
use codec::{Encode, Decode};
use frame_support::{DefaultNoBound, StorageMap, StorageValue};
use sp_runtime::SaturatedConversion;
use sp_std::{collections::btree_map::BTreeMap, marker::PhantomData};

/// Type of voter.
///
/// Similar to [`crate::StakerStatus`], but somewhat more limited.
#[derive(Clone, Copy, Encode, Decode, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum VoterType {
	/// Validator (self-vote)
	Validator,
	/// Nominator
	Nominator,
}

/// Fundamental information about a voter.
#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Voter<AccountId> {
	id: AccountId,
	voter_type: VoterType,
	cache_weight: VoteWeight,
}

impl<T: Config> Pallet<T> {
	/// `Self` accessor for `NominatorList<T>`
	pub fn voter_list() -> VoterList<T> {
		crate::NominatorList::<T>::get()
	}
}

/// Linked list of nominstors, sorted by stake.
#[derive(DefaultNoBound, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct VoterList<T: Config> {
	head: Option<AccountIdOf<T>>,
	tail: Option<AccountIdOf<T>>,
}

impl<T: Config> VoterList<T> {
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

#[derive(Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Node<T: Config> {
	prev: Option<AccountIdOf<T>>,
	next: Option<AccountIdOf<T>>,
	voter: Voter<AccountIdOf<T>>,
}

impl<T: Config> Node<T> {
	/// Get the previous node.
	pub fn prev(&self) -> Option<Node<T>> {
		self.prev.as_ref().and_then(|prev| crate::NominatorNodes::try_get(prev).ok())
	}

	/// Get the next node.
	pub fn next(&self) -> Option<Node<T>> {
		self.next.as_ref().and_then(|next| crate::NominatorNodes::try_get(next).ok())
	}

	/// Get this voter's voting data.
	pub fn voting_data(
		&self,
		weight_of: impl Fn(&T::AccountId) -> VoteWeight,
		slashing_spans: &BTreeMap<AccountIdOf<T>, SlashingSpans>,
	) -> Option<VotingDataOf<T>> {
		match self.voter.voter_type {
			VoterType::Validator => Some((
				self.voter.id.clone(),
				weight_of(&self.voter.id),
				vec![self.voter.id.clone()],
			)),
			VoterType::Nominator => {
				let Nominations { submitted_in, mut targets, .. } =
					Nominators::<T>::get(self.voter.id.clone())?;
				// Filter out nomination targets which were nominated before the most recent
				// slashing span.
				targets.retain(|stash| {
					slashing_spans
						.get(stash)
						.map_or(true, |spans| submitted_in >= spans.last_nonzero_slash())
				});

				(!targets.is_empty())
					.then(move || (self.voter.id.clone(), weight_of(&self.voter.id), targets))
			}
		}
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
