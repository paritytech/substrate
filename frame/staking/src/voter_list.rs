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

#[derive(Debug, thiserror::Error)]
pub enum Error {
	#[error("attempted to insert into the wrong position in the list")]
	WrongInsertPosition,
}

/// Type of voter.
///
/// Similar to [`crate::StakerStatus`], but somewhat more limited.
#[derive(Clone, Copy, Encode, Decode, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum VoterType {
	Validator,
	Nominator,
}

/// Fundamental information about a voter.
#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Voter<AccountId> {
	/// Account Id of this voter
	pub id: AccountId,
	/// Whether the voter is a validator or nominator
	pub voter_type: VoterType,
	/// The current slashable balance this voter brings.
	///
	/// This value is cached because the actual vote weight is likely to change frequently due to
	/// various rewards and slashes, without substantially affecting the overall position in the
	/// list. It's cheaper and easier to operate on a cache than to look up the actual value for
	/// each voter each time.
	pub cache_weight: VoteWeight,
}

pub type VoterOf<T> = Voter<AccountIdOf<T>>;

impl<T: Config> Pallet<T> {
	/// `Self` accessor for `NominatorList<T>`
	pub fn voter_list() -> VoterList<T> {
		VoterList::<T>::get()
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

	/// Get this list from storage.
	pub fn get() -> Self {
		crate::NominatorList::<T>::get()
	}

	/// Update this list in storage.
	pub fn put(self) {
		crate::NominatorList::<T>::put(self);
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

	/// Insert a new voter into the list.
	///
	/// It is always necessary to specify the position in the list into which the voter's node
	/// should be inserted. This ensures that, while _someone_ has to iterate the list to discover
	/// the proper insertion position, that iteration happens off the blockchain.
	///
	/// If `after.is_none()`, then the voter should be inserted at the list head.
	///
	/// This function does _not_ check that `voter.cache_weight` is accurate. That value should be
	/// computed in a higher-level function calling this one.
	///
	/// This is an immediate operation which modifies storage directly.
	pub fn insert(mut self, voter: VoterOf<T>, after: Option<AccountIdOf<T>>) -> Result<(), Error> {
		let predecessor = after.as_ref().and_then(Node::<T>::from_id);
		let successor = after.map_or_else(|| self.head(), |id| Node::<T>::from_id(&id));

		// an insert position is legal if it is not less than its predecessor and not greater than
		// its successor.
		if let Some(predecessor) = predecessor.as_ref() {
			if predecessor.voter.cache_weight < voter.cache_weight {
				return Err(Error::WrongInsertPosition);
			}
		}
		if let Some(successor) = successor.as_ref() {
			if successor.voter.cache_weight > voter.cache_weight {
				return Err(Error::WrongInsertPosition);
			}
		}

		let id = voter.id.clone();

		// insert the actual voter
		let voter_node = Node::<T> {
			voter,
			prev: predecessor.as_ref().map(|prev| prev.voter.id.clone()),
			next: successor.as_ref().map(|next| next.voter.id.clone()),
		};
		voter_node.put();

		// update the list links
		if predecessor.is_none() {
			self.head = Some(id.clone());
		}
		if successor.is_none() {
			self.tail = Some(id.clone());
		}
		self.put();

		// update the node links
		if let Some(mut predecessor) = predecessor {
			predecessor.next = Some(id.clone());
			predecessor.put();

		}
		if let Some(mut successor) = successor {
			successor.prev = Some(id.clone());
			successor.put();
		}

		Ok(())
	}

	/// Remove a voter from the list.
	///
	/// Returns `true` when the voter had previously existed in the list.
	///
	/// This is an immediate operation which modifies storage directly.
	pub fn remove(mut self, id: AccountIdOf<T>) -> Result<bool, Error> {
		let maybe_node = Node::<T>::from_id(&id);
		let existed = maybe_node.is_some();
		if let Some(node) = maybe_node {
			let predecessor = node.prev();
			let successor = node.next();

			let predecessor_id = predecessor.as_ref().map(|prev| prev.voter.id.clone());
			let successor_id = successor.as_ref().map(|next| next.voter.id.clone());

			// update list
			if predecessor.is_none() {
				self.head = successor_id.clone();
			}
			if successor.is_none() {
				self.tail = predecessor_id.clone();
			}
			self.put();

			// update adjacent nodes
			if let Some(mut prev) = predecessor {
				prev.next = successor_id;
				prev.put();
			}
			if let Some(mut next) = successor {
				next.prev = predecessor_id;
				next.put();
			}

			// remove the node itself
			node.remove();
		}
		Ok(existed)
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
	/// Get a node by account id.
	pub fn from_id(id: &AccountIdOf<T>) -> Option<Node<T>> {
		crate::NominatorNodes::<T>::try_get(id).ok()
	}

	/// Update the node in storage.
	pub fn put(self) {
		crate::NominatorNodes::<T>::insert(self.voter.id.clone(), self);
	}

	/// Remove the node from storage.
	///
	/// This function is intentionally private, because it's naive.
	/// [`VoterList::<T>::remove`] is the better option for general use.
	fn remove(self) {
		crate::NominatorNodes::<T>::remove(self.voter.id);
	}

	/// Get the previous node.
	pub fn prev(&self) -> Option<Node<T>> {
		self.prev.as_ref().and_then(Self::from_id)
	}

	/// Get the next node.
	pub fn next(&self) -> Option<Node<T>> {
		self.next.as_ref().and_then(Self::from_id)
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
