// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! A MMR storage implementations.

use codec::Encode;
use frame_support::log;
use mmr_lib::helper;
use sp_io::offchain_index;
#[cfg(not(feature = "std"))]
use sp_std::prelude::Vec;

use crate::{
	mmr::{Node, NodeOf},
	primitives::{self, NodeIndex},
	Config, Nodes, NumberOfLeaves, Pallet,
};

/// A marker type for runtime-specific storage implementation.
///
/// Allows appending new items to the MMR and proof verification.
/// MMR nodes are appended to two different storages:
/// 1. We add nodes (leaves) hashes to the on-chain storage (see [crate::Nodes]).
/// 2. We add full leaves (and all inner nodes as well) into the `IndexingAPI` during block
///    processing, so the values end up in the Offchain DB if indexing is enabled.
pub struct RuntimeStorage;

/// A marker type for offchain-specific storage implementation.
///
/// Allows proof generation and verification, but does not support appending new items.
/// MMR nodes are assumed to be stored in the Off-Chain DB. Note this storage type
/// DOES NOT support adding new items to the MMR.
pub struct OffchainStorage;

/// A storage layer for MMR.
///
/// There are two different implementations depending on the use case.
/// See docs for [RuntimeStorage] and [OffchainStorage].
pub struct Storage<StorageType, T, I, L>(sp_std::marker::PhantomData<(StorageType, T, I, L)>);

impl<StorageType, T, I, L> Default for Storage<StorageType, T, I, L> {
	fn default() -> Self {
		Self(Default::default())
	}
}

impl<T, I, L> mmr_lib::MMRStore<NodeOf<T, I, L>> for Storage<OffchainStorage, T, I, L>
where
	T: Config<I>,
	I: 'static,
	L: primitives::FullLeaf + codec::Decode,
{
	fn get_elem(&self, pos: NodeIndex) -> mmr_lib::Result<Option<NodeOf<T, I, L>>> {
		let key = Pallet::<T, I>::offchain_key(pos);
		// Retrieve the element from Off-chain DB.
		Ok(sp_io::offchain::local_storage_get(sp_core::offchain::StorageKind::PERSISTENT, &key)
			.and_then(|v| codec::Decode::decode(&mut &*v).ok()))
	}

	fn append(&mut self, _: NodeIndex, _: Vec<NodeOf<T, I, L>>) -> mmr_lib::Result<()> {
		panic!("MMR must not be altered in the off-chain context.")
	}
}

impl<T, I, L> mmr_lib::MMRStore<NodeOf<T, I, L>> for Storage<RuntimeStorage, T, I, L>
where
	T: Config<I>,
	I: 'static,
	L: primitives::FullLeaf,
{
	fn get_elem(&self, pos: NodeIndex) -> mmr_lib::Result<Option<NodeOf<T, I, L>>> {
		Ok(<Nodes<T, I>>::get(pos).map(Node::Hash))
	}

	fn append(&mut self, pos: NodeIndex, elems: Vec<NodeOf<T, I, L>>) -> mmr_lib::Result<()> {
		let leaves = crate::NumberOfLeaves::<T, I>::get();
		let size = crate::mmr::utils::NodesUtils::new(leaves).size();

		if pos != size {
			return Err(mmr_lib::Error::InconsistentStore)
		}

		let diff = |a: &[NodeIndex], b: &[NodeIndex]| -> Vec<NodeIndex> {
			b.iter().filter(|x| !a.contains(x)).cloned().collect()
		};
		let elems = elems
			.into_iter()
			.enumerate()
			.map(|(i, elem)| (size + i as NodeIndex, elem))
			.collect::<Vec<_>>();
		let leaves = elems.iter().fold(leaves, |acc, (pos, elem)| {
			// Indexing API is used to store the full leaf content.
			elem.using_encoded(|elem| {
				offchain_index::set(&Pallet::<T, I>::offchain_key(*pos), elem)
			});

			if let Node::Data(..) = elem {
				acc + 1
			} else {
				acc
			}
		});

		NumberOfLeaves::<T, I>::put(leaves);

		let peaks_before = if size == 0 { vec![] } else { helper::get_peaks(size) };
		let peaks_after = helper::get_peaks(size + elems.len() as NodeIndex);
		let nodes_to_prune = diff(&peaks_after, &peaks_before);
		let peaks_to_store = diff(&peaks_before, &peaks_after);

		sp_std::if_std! {
			log::trace!("elems: {:?}\n", elems);
			log::trace!("peaks_before: {:?}", peaks_before);
			log::trace!("peaks_after: {:?}", peaks_after);
			log::trace!("nodes_to_prune: {:?}", nodes_to_prune);
			log::trace!("peaks_to_store: {:?}\n", peaks_to_store);
		}

		for pos in nodes_to_prune {
			<Nodes<T, I>>::remove(pos);
		}
		for pos in peaks_to_store {
			if let Some((_, elem)) = elems.iter().find(|(pos_, _)| *pos_ == pos) {
				<Nodes<T, I>>::insert(pos, elem.hash());

				sp_std::if_std! {
					log::trace!("position: {}, elem: {:?}", pos, elem);
				}
			} else {
				log::error!("The different must existed in `elems`; qed");
			}
		}

		Ok(())
	}
}
