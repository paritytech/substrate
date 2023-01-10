// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! # Node authorization pallet
//!
//! This pallet manages a configurable set of nodes for a permissioned network.
//! Each node is dentified by a PeerId (i.e. `Vec<u8>`). It provides two ways to
//! authorize a node,
//!
//! - a set of well known nodes across different organizations in which the
//! connections are allowed.
//! - users can claim the ownership for each node, then manage the connections of
//! the node.
//!
//! A node must have an owner. The owner can additionally change the connections
//! for the node. Only one user is allowed to claim a specific node. To eliminate
//! false claim, the maintainer of the node should claim it before even starting the
//! node. This pallet uses offchain worker to set reserved nodes, if the node is not
//! an authority, make sure to enable offchain worker with the right CLI flag. The
//! node can be lagged with the latest block, in this case you need to disable offchain
//! worker and manually set reserved nodes when starting it.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

pub mod weights;

use frame_support::{traits::Defensive, BoundedBTreeSet};
pub use pallet::*;
use sp_core::OpaquePeerId as PeerId;
use sp_runtime::traits::StaticLookup;
use sp_std::{collections::btree_set::BTreeSet, prelude::*};
pub use weights::WeightInfo;

type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	/// The module configuration trait
	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The maximum number of well known nodes that are allowed to set
		#[pallet::constant]
		type MaxWellKnownNodes: Get<u32>;

		/// The maximum length in bytes of PeerId
		#[pallet::constant]
		type MaxPeerIdLength: Get<u32>;

		/// The maximum number of additional connections that are allowed to be set
		#[pallet::constant]
		type MaxAdditionalConnections: Get<u32>;

		/// The origin which can add a well known node.
		type AddOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The origin which can remove a well known node.
		type RemoveOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The origin which can swap the well known nodes.
		type SwapOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The origin which can reset the well known nodes.
		type ResetOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	/// A bounded opaque peer ID.
	#[derive(Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	#[codec(mel_bound())]
	#[scale_info(skip_type_params(T))]
	pub struct BoundedPeerId<T: Config>(BoundedVec<u8, T::MaxPeerIdLength>);

	impl<T: Config> PartialEq for BoundedPeerId<T> {
		fn eq(&self, rhs: &Self) -> bool {
			self.0.eq(&rhs.0)
		}
	}
	impl<T: Config> Eq for BoundedPeerId<T> {}
	impl<T: Config> PartialOrd for BoundedPeerId<T> {
		fn partial_cmp(&self, rhs: &Self) -> Option<std::cmp::Ordering> {
			Some(self.0.cmp(&rhs.0))
		}
	}
	impl<T: Config> Ord for BoundedPeerId<T> {
		fn cmp(&self, rhs: &Self) -> std::cmp::Ordering {
			self.0.cmp(&rhs.0)
		}
	}
	impl<T: Config> Clone for BoundedPeerId<T> {
		fn clone(&self) -> Self {
			BoundedPeerId(self.0.clone())
		}
	}

	impl<T: Config> TryFrom<PeerId> for BoundedPeerId<T> {
		type Error = Error<T>;
		fn try_from(id: PeerId) -> Result<Self, Self::Error> {
			BoundedVec::try_from(id.0)
				.map_err(|_| Error::<T>::PeerIdTooLong)
				.map(BoundedPeerId::<T>)
		}
	}

	impl<T: Config> From<BoundedPeerId<T>> for PeerId {
		fn from(id: BoundedPeerId<T>) -> Self {
			PeerId(id.0.into())
		}
	}

	/// The set of well known nodes. This is stored sorted (just by value).
	#[pallet::storage]
	#[pallet::getter(fn well_known_nodes)]
	pub type WellKnownNodes<T: Config> =
		StorageValue<_, BoundedBTreeSet<BoundedPeerId<T>, T::MaxWellKnownNodes>, ValueQuery>;

	/// A map that maintains the ownership of each node.
	#[pallet::storage]
	#[pallet::getter(fn owners)]
	pub type Owners<T: Config> = StorageMap<_, Blake2_128Concat, BoundedPeerId<T>, T::AccountId>;

	/// The additional adapative connections of each node.
	#[pallet::storage]
	#[pallet::getter(fn additional_connection)]
	pub type AdditionalConnections<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		BoundedPeerId<T>,
		BoundedBTreeSet<BoundedPeerId<T>, T::MaxAdditionalConnections>,
		ValueQuery,
	>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub nodes: Vec<(PeerId, T::AccountId)>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			Self { nodes: Vec::new() }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			if let Err(error) = Pallet::<T>::initialize_nodes(&self.nodes) {
				panic!("Failed to initialize node-authorization pallet on genesis: {:?}", error);
			}
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// The given well known node was added.
		NodeAdded { peer_id: PeerId, who: T::AccountId },
		/// The given well known node was removed.
		NodeRemoved { peer_id: PeerId },
		/// The given well known node was swapped; first item was removed,
		/// the latter was added.
		NodeSwapped { removed: PeerId, added: PeerId },
		/// The given well known nodes were reset.
		NodesReset { nodes: Vec<(PeerId, T::AccountId)> },
		/// The given node was claimed by a user.
		NodeClaimed { peer_id: PeerId, who: T::AccountId },
		/// The given claim was removed by its owner.
		ClaimRemoved { peer_id: PeerId, who: T::AccountId },
		/// The node was transferred to another account.
		NodeTransferred { peer_id: PeerId, target: T::AccountId },
		/// The allowed connections were added to a node.
		ConnectionsAdded { peer_id: PeerId, allowed_connections: Vec<PeerId> },
		/// The allowed connections were removed from a node.
		ConnectionsRemoved { peer_id: PeerId, allowed_connections: Vec<PeerId> },
	}

	#[pallet::error]
	pub enum Error<T> {
		/// The PeerId is too long.
		PeerIdTooLong,
		/// Too many well known nodes.
		TooManyNodes,
		/// The node is already joined in the list.
		AlreadyJoined,
		/// The node doesn't exist in the list.
		NotExist,
		/// The node is already claimed by a user.
		AlreadyClaimed,
		/// The node hasn't been claimed yet.
		NotClaimed,
		/// You are not the owner of the node.
		NotOwner,
		/// No permisson to perform specific operation.
		PermissionDenied,
		/// Too many additional connections.
		TooManyAdditionalConnections,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		/// Set reserved node every block. It may not be enabled depends on the offchain
		/// worker settings when starting the node.
		fn offchain_worker(now: T::BlockNumber) {
			let network_state = sp_io::offchain::network_state();
			match network_state {
				Err(_) => log::error!(
					target: "runtime::node-authorization",
					"Error: failed to get network state of node at {:?}",
					now,
				),
				Ok(state) => {
					let encoded_peer = state.peer_id.0;
					match Decode::decode(&mut &encoded_peer[..]) {
						Err(_) => log::error!(
							target: "runtime::node-authorization",
							"Error: failed to decode PeerId at {:?}",
							now,
						),
						Ok(node) =>
							if let Ok(node) = BoundedPeerId::<T>::try_from(PeerId(node)) {
								sp_io::offchain::set_authorized_nodes(
									Self::get_authorized_nodes(&node),
									true,
								)
							} else {
								log::error!(
									target: "runtime::node-authorization",
									"Error: PeerId is too long at {:?}",
									now,
								)
							},
					}
				},
			}
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Add a node to the set of well known nodes. If the node is already claimed, the owner
		/// will be updated and keep the existing additional connection unchanged.
		///
		/// May only be called from `T::AddOrigin`.
		///
		/// - `node`: identifier of the node.
		#[pallet::call_index(0)]
		#[pallet::weight((T::WeightInfo::add_well_known_node(), DispatchClass::Operational))]
		pub fn add_well_known_node(
			origin: OriginFor<T>,
			node: PeerId,
			owner: AccountIdLookupOf<T>,
		) -> DispatchResult {
			T::AddOrigin::ensure_origin(origin)?;
			let owner = T::Lookup::lookup(owner)?;
			let node = BoundedPeerId::<T>::try_from(node)?;

			let mut nodes = WellKnownNodes::<T>::get();
			ensure!(!nodes.contains(&node), Error::<T>::AlreadyJoined);
			nodes.try_insert(node.clone()).map_err(|_| Error::<T>::TooManyNodes)?;

			WellKnownNodes::<T>::put(&nodes);
			<Owners<T>>::insert(&node, &owner);

			Self::deposit_event(Event::NodeAdded { peer_id: node.into(), who: owner });
			Ok(())
		}

		/// Remove a node from the set of well known nodes. The ownership and additional
		/// connections of the node will also be removed.
		///
		/// May only be called from `T::RemoveOrigin`.
		///
		/// - `node`: identifier of the node.
		#[pallet::call_index(1)]
		#[pallet::weight((T::WeightInfo::remove_well_known_node(), DispatchClass::Operational))]
		pub fn remove_well_known_node(origin: OriginFor<T>, node: PeerId) -> DispatchResult {
			T::RemoveOrigin::ensure_origin(origin)?;
			let node = BoundedPeerId::<T>::try_from(node)?;

			let mut nodes = WellKnownNodes::<T>::get();
			ensure!(nodes.contains(&node), Error::<T>::NotExist);

			nodes.remove(&node);

			WellKnownNodes::<T>::put(&nodes);
			<Owners<T>>::remove(&node);
			AdditionalConnections::<T>::remove(&node);

			Self::deposit_event(Event::NodeRemoved { peer_id: node.into() });
			Ok(())
		}

		/// Swap a well known node to another. Both the ownership and additional connections
		/// stay untouched.
		///
		/// May only be called from `T::SwapOrigin`.
		///
		/// - `remove`: the node which will be moved out from the list.
		/// - `add`: the node which will be put in the list.
		#[pallet::call_index(2)]
		#[pallet::weight((T::WeightInfo::swap_well_known_node(), DispatchClass::Operational))]
		pub fn swap_well_known_node(
			origin: OriginFor<T>,
			remove: PeerId,
			add: PeerId,
		) -> DispatchResult {
			T::SwapOrigin::ensure_origin(origin)?;
			let remove = BoundedPeerId::<T>::try_from(remove)?;
			let add = BoundedPeerId::<T>::try_from(add)?;

			if remove == add {
				return Ok(())
			}

			let mut nodes = WellKnownNodes::<T>::get();
			ensure!(nodes.contains(&remove), Error::<T>::NotExist);
			ensure!(!nodes.contains(&add), Error::<T>::AlreadyJoined);

			nodes.remove(&remove);
			nodes
				.try_insert(add.clone())
				.map_err(|_| ())
				.defensive_proof("swapping the nodes doesn't change the number of nodes")
				.map_err(|_| Error::<T>::TooManyNodes)?;

			WellKnownNodes::<T>::put(&nodes);
			Owners::<T>::swap(&remove, &add);
			AdditionalConnections::<T>::swap(&remove, &add);

			Self::deposit_event(Event::NodeSwapped { removed: remove.into(), added: add.into() });
			Ok(())
		}

		/// Reset all the well known nodes. This will not remove the ownership and additional
		/// connections for the removed nodes. The node owner can perform further cleaning if
		/// they decide to leave the network.
		///
		/// May only be called from `T::ResetOrigin`.
		///
		/// - `nodes`: the new nodes for the allow list.
		#[pallet::call_index(3)]
		#[pallet::weight((T::WeightInfo::reset_well_known_nodes(), DispatchClass::Operational))]
		pub fn reset_well_known_nodes(
			origin: OriginFor<T>,
			nodes: Vec<(PeerId, T::AccountId)>,
		) -> DispatchResult {
			T::ResetOrigin::ensure_origin(origin)?;

			Self::initialize_nodes(&nodes)?;
			Self::deposit_event(Event::NodesReset { nodes });
			Ok(())
		}

		/// A given node can be claimed by anyone. The owner should be the first to know its
		/// PeerId, so claim it right away!
		///
		/// - `node`: identifier of the node.
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::claim_node())]
		pub fn claim_node(origin: OriginFor<T>, node: PeerId) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			let node = BoundedPeerId::<T>::try_from(node)?;
			ensure!(!Owners::<T>::contains_key(&node), Error::<T>::AlreadyClaimed);

			Owners::<T>::insert(&node, &sender);
			Self::deposit_event(Event::NodeClaimed { peer_id: node.into(), who: sender });
			Ok(())
		}

		/// A claim can be removed by its owner and get back the reservation. The additional
		/// connections are also removed. You can't remove a claim on well known nodes, as it
		/// needs to reach consensus among the network participants.
		///
		/// - `node`: identifier of the node.
		#[pallet::call_index(5)]
		#[pallet::weight(T::WeightInfo::remove_claim())]
		pub fn remove_claim(origin: OriginFor<T>, node: PeerId) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			let node = BoundedPeerId::<T>::try_from(node)?;
			let owner = Owners::<T>::get(&node).ok_or(Error::<T>::NotClaimed)?;
			ensure!(owner == sender, Error::<T>::NotOwner);
			ensure!(!WellKnownNodes::<T>::get().contains(&node), Error::<T>::PermissionDenied);

			Owners::<T>::remove(&node);
			AdditionalConnections::<T>::remove(&node);

			Self::deposit_event(Event::ClaimRemoved { peer_id: node.into(), who: sender });
			Ok(())
		}

		/// A node can be transferred to a new owner.
		///
		/// - `node`: identifier of the node.
		/// - `owner`: new owner of the node.
		#[pallet::call_index(6)]
		#[pallet::weight(T::WeightInfo::transfer_node())]
		pub fn transfer_node(
			origin: OriginFor<T>,
			node: PeerId,
			owner: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let owner = T::Lookup::lookup(owner)?;

			let node = BoundedPeerId::<T>::try_from(node)?;
			let pre_owner = Owners::<T>::get(&node).ok_or(Error::<T>::NotClaimed)?;
			ensure!(pre_owner == sender, Error::<T>::NotOwner);

			Owners::<T>::insert(&node, &owner);

			Self::deposit_event(Event::NodeTransferred { peer_id: node.into(), target: owner });
			Ok(())
		}

		/// Add additional connections to a given node.
		///
		/// - `node`: identifier of the node.
		/// - `connections`: additonal nodes from which the connections are allowed.
		#[pallet::call_index(7)]
		#[pallet::weight(T::WeightInfo::add_connections())]
		pub fn add_connections(
			origin: OriginFor<T>,
			node: PeerId,
			connections: Vec<PeerId>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			let node = BoundedPeerId::<T>::try_from(node)?;
			let owner = Owners::<T>::get(&node).ok_or(Error::<T>::NotClaimed)?;
			ensure!(owner == sender, Error::<T>::NotOwner);

			let mut nodes: BTreeSet<_> = AdditionalConnections::<T>::get(&node).into();
			for add_node in connections.iter() {
				if add_node.0 == node.0.as_slice() {
					continue
				}

				nodes.insert(BoundedPeerId::<T>::try_from(add_node.clone())?);
			}

			let nodes: BoundedBTreeSet<_, _> =
				nodes.try_into().map_err(|_| Error::<T>::TooManyAdditionalConnections)?;
			AdditionalConnections::<T>::insert(&node, nodes);

			Self::deposit_event(Event::ConnectionsAdded {
				peer_id: node.into(),
				allowed_connections: connections,
			});
			Ok(())
		}

		/// Remove additional connections of a given node.
		///
		/// - `node`: identifier of the node.
		/// - `connections`: additonal nodes from which the connections are not allowed anymore.
		#[pallet::call_index(8)]
		#[pallet::weight(T::WeightInfo::remove_connections())]
		pub fn remove_connections(
			origin: OriginFor<T>,
			node: PeerId,
			connections: Vec<PeerId>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			let node = BoundedPeerId::<T>::try_from(node)?;
			let owner = Owners::<T>::get(&node).ok_or(Error::<T>::NotClaimed)?;
			ensure!(owner == sender, Error::<T>::NotOwner);

			let mut nodes = AdditionalConnections::<T>::get(&node);
			for remove_node in connections.iter() {
				let remove_node = BoundedPeerId::<T>::try_from(remove_node.clone())?;
				nodes.remove(&remove_node);
			}

			AdditionalConnections::<T>::insert(&node, nodes);

			Self::deposit_event(Event::ConnectionsRemoved {
				peer_id: node.into(),
				allowed_connections: connections,
			});
			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	fn initialize_nodes(nodes: &Vec<(PeerId, T::AccountId)>) -> Result<(), Error<T>> {
		let mut peer_ids = BoundedBTreeSet::new();
		let mut owners = Vec::new();
		for (peer_id, account_id) in nodes {
			let peer_id = BoundedPeerId::<T>::try_from(peer_id.clone())?;
			peer_ids.try_insert(peer_id.clone()).map_err(|_| Error::<T>::TooManyNodes)?;
			owners.push((peer_id, account_id));
		}

		WellKnownNodes::<T>::put(&peer_ids);
		for (peer_id, account_id) in owners {
			Owners::<T>::insert(peer_id, account_id);
		}

		Ok(())
	}

	fn get_authorized_nodes(node: &BoundedPeerId<T>) -> Vec<PeerId> {
		let mut nodes: Vec<_> = AdditionalConnections::<T>::get(node)
			.into_iter()
			.map(|node| node.into())
			.collect();

		let mut well_known_nodes = WellKnownNodes::<T>::get();
		if well_known_nodes.contains(node) {
			well_known_nodes.remove(node);
			nodes.extend(well_known_nodes.into_iter().map(|node| node.into()));
		}

		nodes
	}
}
