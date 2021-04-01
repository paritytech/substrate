// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Some helper functions/macros for this crate.

use super::{Config, VoteWeight, CompactVoterIndexOf, CompactTargetIndexOf};
use sp_std::{collections::btree_map::BTreeMap, convert::TryInto, boxed::Box, prelude::*};

#[macro_export]
macro_rules! log {
	($level:tt, $pattern:expr $(, $values:expr)* $(,)?) => {
		log::$level!(
			target: $crate::LOG_TARGET,
			concat!("[#{:?}] 🗳  ", $pattern), <frame_system::Module<T>>::block_number() $(, $values)*
		)
	};
}

/// Generate a btree-map cache of the voters and their indices.
///
/// This can be used to efficiently build index getter closures.
pub fn generate_voter_cache<T: Config>(
	snapshot: &Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>,
) -> BTreeMap<T::AccountId, usize> {
	let mut cache: BTreeMap<T::AccountId, usize> = BTreeMap::new();
	snapshot.iter().enumerate().for_each(|(i, (x, _, _))| {
		let _existed = cache.insert(x.clone(), i);
		// if a duplicate exists, we only consider the last one. Defensive only, should never
		// happen.
		debug_assert!(_existed.is_none());
	});

	cache
}

/// Create a function the returns the index a voter in the snapshot.
///
/// The returning index type is the same as the one defined in `T::CompactSolution::Voter`.
///
/// ## Warning
///
/// The snapshot must be the same is the one used to create `cache`.
pub fn voter_index_fn<T: Config>(
	cache: &BTreeMap<T::AccountId, usize>,
) -> Box<dyn Fn(&T::AccountId) -> Option<CompactVoterIndexOf<T>> + '_> {
	Box::new(move |who| {
		cache.get(who).and_then(|i| <usize as TryInto<CompactVoterIndexOf<T>>>::try_into(*i).ok())
	})
}

/// Same as [`voter_index_fn`], but the returning index is converted into usize, if possible.
///
/// ## Warning
///
/// The snapshot must be the same is the one used to create `cache`.
pub fn voter_index_fn_usize<T: Config>(
	cache: &BTreeMap<T::AccountId, usize>,
) -> Box<dyn Fn(&T::AccountId) -> Option<usize> + '_> {
	Box::new(move |who| cache.get(who).cloned())
}

/// A non-optimized, linear version of [`voter_index_fn`] that does not need a cache and does a
/// linear search.
///
/// ## Warning
///
/// Not meant to be used in production.
pub fn voter_index_fn_linear<T: Config>(
	snapshot: &Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>,
) -> Box<dyn Fn(&T::AccountId) -> Option<CompactVoterIndexOf<T>> + '_> {
	Box::new(move |who| {
		snapshot
			.iter()
			.position(|(x, _, _)| x == who)
			.and_then(|i| <usize as TryInto<CompactVoterIndexOf<T>>>::try_into(i).ok())
	})
}

/// Create a function the returns the index a targets in the snapshot.
///
/// The returning index type is the same as the one defined in `T::CompactSolution::Target`.
pub fn target_index_fn_linear<T: Config>(
	snapshot: &Vec<T::AccountId>,
) -> Box<dyn Fn(&T::AccountId) -> Option<CompactTargetIndexOf<T>> + '_> {
	Box::new(move |who| {
		snapshot
			.iter()
			.position(|x| x == who)
			.and_then(|i| <usize as TryInto<CompactTargetIndexOf<T>>>::try_into(i).ok())
	})
}

/// Create a function that can map a voter index ([`CompactVoterIndexOf`]) to the actual voter
/// account using a linearly indexible snapshot.
pub fn voter_at_fn<T: Config>(
	snapshot: &Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>,
) -> Box<dyn Fn(CompactVoterIndexOf<T>) -> Option<T::AccountId> + '_> {
	Box::new(move |i| {
		<CompactVoterIndexOf<T> as TryInto<usize>>::try_into(i)
			.ok()
			.and_then(|i| snapshot.get(i).map(|(x, _, _)| x).cloned())
	})
}

/// Create a function that can map a target index ([`CompactTargetIndexOf`]) to the actual target
/// account using a linearly indexible snapshot.
pub fn target_at_fn<T: Config>(
	snapshot: &Vec<T::AccountId>,
) -> Box<dyn Fn(CompactTargetIndexOf<T>) -> Option<T::AccountId> + '_> {
	Box::new(move |i| {
		<CompactTargetIndexOf<T> as TryInto<usize>>::try_into(i)
			.ok()
			.and_then(|i| snapshot.get(i).cloned())
	})
}

/// Create a function to get the stake of a voter.
///
/// This is not optimized and uses a linear search.
pub fn stake_of_fn_linear<T: Config>(
	snapshot: &Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>,
) -> Box<dyn Fn(&T::AccountId) -> VoteWeight + '_> {
	Box::new(move |who| {
		snapshot.iter().find(|(x, _, _)| x == who).map(|(_, x, _)| *x).unwrap_or_default()
	})
}

/// Create a function to get the stake of a voter.
///
/// ## Warning
///
/// The cache need must be derived from the same snapshot. Zero is returned if a voter is
/// non-existent.
pub fn stake_of_fn<'a, T: Config>(
	snapshot: &'a Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>,
	cache: &'a BTreeMap<T::AccountId, usize>,
) -> Box<dyn Fn(&T::AccountId) -> VoteWeight + 'a> {
	Box::new(move |who| {
		if let Some(index) = cache.get(who) {
			snapshot.get(*index).map(|(_, x, _)| x).cloned().unwrap_or_default()
		} else {
			0
		}
	})
}
