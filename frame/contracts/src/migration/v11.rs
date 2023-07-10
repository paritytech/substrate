// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Overflowing bounded DeletionQueue.
//! See <https://github.com/paritytech/substrate/pull/13702>.

use crate::{
	migration::{IsFinished, MigrationStep},
	weights::WeightInfo,
	Config, Pallet, TrieId, Weight, LOG_TARGET,
};
#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;

use codec::{Decode, Encode};
use frame_support::{codec, pallet_prelude::*, storage_alias, DefaultNoBound};
use sp_std::{marker::PhantomData, prelude::*};
mod old {
	use super::*;

	#[derive(Encode, Decode, TypeInfo, MaxEncodedLen)]
	pub struct DeletedContract {
		pub(crate) trie_id: TrieId,
	}

	#[storage_alias]
	pub type DeletionQueue<T: Config> = StorageValue<Pallet<T>, Vec<DeletedContract>>;
}

#[derive(Encode, Decode, TypeInfo, MaxEncodedLen, DefaultNoBound, Clone)]
#[scale_info(skip_type_params(T))]
pub struct DeletionQueueManager<T: Config> {
	insert_counter: u32,
	delete_counter: u32,
	_phantom: PhantomData<T>,
}

#[cfg(any(feature = "runtime-benchmarks", feature = "try-runtime"))]
pub fn fill_old_queue<T: Config>(len: usize) {
	let queue: Vec<old::DeletedContract> =
		core::iter::repeat_with(|| old::DeletedContract { trie_id: Default::default() })
			.take(len)
			.collect();
	old::DeletionQueue::<T>::set(Some(queue));
}

#[storage_alias]
type DeletionQueue<T: Config> = StorageMap<Pallet<T>, Twox64Concat, u32, TrieId>;

#[storage_alias]
type DeletionQueueCounter<T: Config> = StorageValue<Pallet<T>, DeletionQueueManager<T>, ValueQuery>;

#[derive(Encode, Decode, MaxEncodedLen, DefaultNoBound)]
pub struct Migration<T: Config> {
	_phantom: PhantomData<T>,
}

impl<T: Config> MigrationStep for Migration<T> {
	const VERSION: u16 = 11;

	// It would be more correct to make our use the now removed [DeletionQueueDepth](https://github.com/paritytech/substrate/pull/13702/files#diff-70e9723e9db62816e35f6f885b6770a8449c75a6c2733e9fa7a245fe52c4656c)
	// but in practice the queue is always empty, so 128 is a good enough approximation for not
	// underestimating the weight of our migration.
	fn max_step_weight() -> Weight {
		T::WeightInfo::v11_migration_step(128)
	}

	fn step(&mut self) -> (IsFinished, Weight) {
		let Some(old_queue) = old::DeletionQueue::<T>::take() else {
			return (IsFinished::Yes, Weight::zero())
		};
		let len = old_queue.len();

		log::debug!(
			target: LOG_TARGET,
			"Migrating deletion queue with {} deleted contracts",
			old_queue.len()
		);

		if !old_queue.is_empty() {
			let mut queue = DeletionQueueManager::<T>::default();
			for contract in old_queue {
				<DeletionQueue<T>>::insert(queue.insert_counter, contract.trie_id);
				queue.insert_counter += 1;
			}

			<DeletionQueueCounter<T>>::set(queue);
		}

		(IsFinished::Yes, T::WeightInfo::v11_migration_step(len as u32))
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade_step() -> Result<Vec<u8>, TryRuntimeError> {
		let old_queue = old::DeletionQueue::<T>::take().unwrap_or_default();

		if old_queue.is_empty() {
			let len = 10u32;
			log::debug!(
				target: LOG_TARGET,
				"Injecting {len} entries to deletion queue to test migration"
			);
			fill_old_queue::<T>(len as usize);
			return Ok(len.encode())
		}

		Ok((old_queue.len() as u32).encode())
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade_step(state: Vec<u8>) -> Result<(), TryRuntimeError> {
		let len = <u32 as Decode>::decode(&mut &state[..])
			.expect("pre_upgrade_step provides a valid state; qed");
		let counter = <DeletionQueueCounter<T>>::get();
		ensure!(counter.insert_counter == len, "invalid insert counter");
		ensure!(counter.delete_counter == 0, "invalid delete counter");
		Ok(())
	}
}
