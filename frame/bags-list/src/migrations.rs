// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! The migrations of this pallet.

use codec::{Decode, Encode};
use core::marker::PhantomData;
use frame_election_provider_support::ScoreProvider;
use frame_support::traits::OnRuntimeUpgrade;
use sp_runtime::traits::Zero;

#[cfg(feature = "try-runtime")]
use frame_support::ensure;

/// A struct that does not migration, but only checks that the counter prefix exists and is correct.
pub struct CheckCounterPrefix<T: crate::Config<I>, I: 'static>(sp_std::marker::PhantomData<(T, I)>);
impl<T: crate::Config<I>, I: 'static> OnRuntimeUpgrade for CheckCounterPrefix<T, I> {
	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		frame_support::weights::Weight::zero()
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<(), &'static str> {
		// The old explicit storage item.
		#[frame_support::storage_alias]
		type CounterForListNodes<T: crate::Config<I>, I: 'static> =
			StorageValue<crate::Pallet<T, I>, u32>;

		// ensure that a value exists in the counter struct.
		ensure!(
			crate::ListNodes::<T, I>::count() == CounterForListNodes::<T, I>::get().unwrap(),
			"wrong list node counter"
		);

		crate::log!(
			info,
			"checked bags-list prefix to be correct and have {} nodes",
			crate::ListNodes::<T, I>::count()
		);

		Ok(())
	}
}

mod old {
	use super::*;
	use frame_support::pallet_prelude::*;

	#[derive(Encode, Decode)]
	pub struct PreScoreNode<T: crate::Config<I>, I: 'static = ()> {
		pub id: T::AccountId,
		pub prev: Option<T::AccountId>,
		pub next: Option<T::AccountId>,
		pub bag_upper: T::Score,
		#[codec(skip)]
		pub _phantom: PhantomData<I>,
	}

	#[frame_support::storage_alias]
	pub type ListNodes<T: crate::Config<I>, I: 'static> = StorageMap<
		crate::Pallet<T, I>,
		Twox64Concat,
		<T as frame_system::Config>::AccountId,
		PreScoreNode<T, I>,
	>;

	#[frame_support::storage_alias]
	pub type CounterForListNodes<T: crate::Config<I>, I: 'static> =
		StorageValue<crate::Pallet<T, I>, u32, ValueQuery>;

	#[frame_support::storage_alias]
	pub type TempStorage<T: crate::Config<I>, I: 'static> =
		StorageValue<crate::Pallet<T, I>, u32, ValueQuery>;
}

/// A struct that migrates all bags lists to contain a score value.
pub struct AddScore<T: crate::Config<I>, I: 'static = ()>(sp_std::marker::PhantomData<(T, I)>);
impl<T: crate::Config<I>, I: 'static> OnRuntimeUpgrade for AddScore<T, I> {
	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<(), &'static str> {
		// The list node data should be corrupt at this point, so this is zero.
		ensure!(crate::ListNodes::<T, I>::iter().count() == 0, "list node data is not corrupt");
		// We can use the helper `old::ListNode` to get the existing data.
		let iter_node_count: u32 = old::ListNodes::<T, I>::iter().count() as u32;
		let tracked_node_count: u32 = old::CounterForListNodes::<T, I>::get();
		crate::log!(info, "number of nodes before: {:?} {:?}", iter_node_count, tracked_node_count);
		ensure!(iter_node_count == tracked_node_count, "Node count is wrong.");
		old::TempStorage::<T, I>::put(iter_node_count);
		Ok(())
	}

	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		for (_key, node) in old::ListNodes::<T, I>::iter() {
			let score = T::ScoreProvider::score(&node.id);

			let new_node = crate::Node {
				id: node.id.clone(),
				prev: node.prev,
				next: node.next,
				bag_upper: node.bag_upper,
				score,
				_phantom: node._phantom,
			};

			crate::ListNodes::<T, I>::insert(node.id, new_node);
		}

		return frame_support::weights::Weight::MAX
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade() -> Result<(), &'static str> {
		let node_count_before = old::TempStorage::<T, I>::take();
		// Now, the list node data is not corrupt anymore.
		let iter_node_count_after: u32 = crate::ListNodes::<T, I>::iter().count() as u32;
		let tracked_node_count_after: u32 = crate::ListNodes::<T, I>::count();
		crate::log!(
			info,
			"number of nodes after: {:?} {:?}",
			iter_node_count_after,
			tracked_node_count_after,
		);
		ensure!(iter_node_count_after == node_count_before, "Not all nodes were migrated.");
		ensure!(tracked_node_count_after == iter_node_count_after, "Node count is wrong.");
		Ok(())
	}
}
