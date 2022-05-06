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
use frame_support::{ensure, storage::migration, traits::OnRuntimeUpgrade};
use sp_runtime::traits::Zero;

/// A struct that does not migration, but only checks that the counter prefix exists and is correct.
pub struct CheckCounterPrefix<T: crate::Config<I>, I: 'static>(sp_std::marker::PhantomData<(T, I)>);
impl<T: crate::Config<I>, I: 'static> OnRuntimeUpgrade for CheckCounterPrefix<T, I> {
	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		0
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<(), &'static str> {
		// The old explicit storage item.
		frame_support::generate_storage_alias!(BagsList, CounterForListNodes => Value<u32>);

		// ensure that a value exists in the counter struct.
		ensure!(
			crate::ListNodes::<T, I>::count() == CounterForListNodes::get().unwrap(),
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

#[derive(Encode, Decode)]
struct PreScoreNode<T: crate::Config<I>, I: 'static = ()> {
	pub id: T::AccountId,
	pub prev: Option<T::AccountId>,
	pub next: Option<T::AccountId>,
	pub bag_upper: T::Score,
	#[codec(skip)]
	pub _phantom: PhantomData<I>,
}

/// A struct that migrates all bags lists to contain a score value.
pub struct AddScore<T: crate::Config<I>, I: 'static>(sp_std::marker::PhantomData<(T, I)>);
impl<T: crate::Config<I>, I: 'static> OnRuntimeUpgrade for AddScore<T, I> {
	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<(), &'static str> {
		// Nothing that can really be checked here...
		Ok(())
	}

	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		let old_nodes = migration::storage_iter::<PreScoreNode<T, I>>(b"VoterList", b"ListNodes");

		for (_key, node) in old_nodes.drain() {
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
		ensure!(
			crate::ListNodes::<T, I>::iter().count() > 0,
			"Items do not exist where some were expected."
		);
		for (_id, node) in crate::ListNodes::<T, I>::iter() {
			ensure!(!node.score.is_zero(), "Score should be greater than zero");
		}
		Ok(())
	}
}
