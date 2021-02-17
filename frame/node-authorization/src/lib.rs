// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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
//! Each node is dentified by a PeerId (i.e. Vec<u8>). It provides two ways to
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

use sp_core::OpaquePeerId as PeerId;
use sp_std::{
	collections::btree_set::BTreeSet,
	iter::FromIterator,
	prelude::*,
};
use codec::Decode;
use frame_support::{
	decl_module, decl_storage, decl_event, decl_error,
	debug, ensure,
	weights::{DispatchClass, Weight},
	traits::{Get, EnsureOrigin},
};
use frame_system::ensure_signed;

pub trait WeightInfo {
	fn add_well_known_node() -> Weight;
	fn remove_well_known_node() -> Weight;
	fn swap_well_known_node() -> Weight;
	fn reset_well_known_nodes() -> Weight;
	fn claim_node() -> Weight;
	fn remove_claim() -> Weight;
	fn transfer_node() -> Weight;
	fn add_connections() -> Weight;
	fn remove_connections() -> Weight;
}

impl WeightInfo for () {
	fn add_well_known_node() -> Weight { 50_000_000 }
	fn remove_well_known_node() -> Weight { 50_000_000 }
	fn swap_well_known_node() -> Weight { 50_000_000 }
	fn reset_well_known_nodes() -> Weight { 50_000_000 }
	fn claim_node() -> Weight { 50_000_000 }
	fn remove_claim() -> Weight { 50_000_000 }
	fn transfer_node() -> Weight { 50_000_000 }
	fn add_connections() -> Weight { 50_000_000 }
	fn remove_connections() -> Weight { 50_000_000 }
}

pub trait Config: frame_system::Config {
	/// The event type of this module.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Config>::Event>;

	/// The maximum number of well known nodes that are allowed to set
	type MaxWellKnownNodes: Get<u32>;

	/// The maximum length in bytes of PeerId
	type MaxPeerIdLength: Get<u32>;

	/// The origin which can add a well known node.
	type AddOrigin: EnsureOrigin<Self::Origin>;

	/// The origin which can remove a well known node.
	type RemoveOrigin: EnsureOrigin<Self::Origin>;

	/// The origin which can swap the well known nodes.
	type SwapOrigin: EnsureOrigin<Self::Origin>;

	/// The origin which can reset the well known nodes.
	type ResetOrigin: EnsureOrigin<Self::Origin>;

	/// Weight information for extrinsics in this pallet.
	type WeightInfo: WeightInfo;
}

decl_storage! {
	trait Store for Module<T: Config> as NodeAuthorization {
		/// The set of well known nodes. This is stored sorted (just by value).
		pub WellKnownNodes get(fn well_known_nodes): BTreeSet<PeerId>;
		/// A map that maintains the ownership of each node.
		pub Owners get(fn owners):
			map hasher(blake2_128_concat) PeerId => T::AccountId;
		/// The additional adapative connections of each node.
		pub AdditionalConnections get(fn additional_connection):
			map hasher(blake2_128_concat) PeerId => BTreeSet<PeerId>;
	}
	add_extra_genesis {
		config(nodes): Vec<(PeerId, T::AccountId)>;
		build(|config: &GenesisConfig<T>| {
			<Module<T>>::initialize_nodes(&config.nodes)
		})
	}
}

decl_event! {
	pub enum Event<T> where
		<T as frame_system::Config>::AccountId,
	{
		/// The given well known node was added.
		NodeAdded(PeerId, AccountId),
		/// The given well known node was removed.
		NodeRemoved(PeerId),
		/// The given well known node was swapped; first item was removed,
		/// the latter was added.
		NodeSwapped(PeerId, PeerId),
		/// The given well known nodes were reset.
		NodesReset(Vec<(PeerId, AccountId)>),
		/// The given node was claimed by a user.
		NodeClaimed(PeerId, AccountId),
		/// The given claim was removed by its owner.
		ClaimRemoved(PeerId, AccountId),
		/// The node was transferred to another account.
		NodeTransferred(PeerId, AccountId),
		/// The allowed connections were added to a node.
		ConnectionsAdded(PeerId, Vec<PeerId>),
		/// The allowed connections were removed from a node.
		ConnectionsRemoved(PeerId, Vec<PeerId>),
	}
}

decl_error! {
	/// Error for the node authorization module.
	pub enum Error for Module<T: Config> {
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
	}
}

decl_module! {
	pub struct Module<T: Config> for enum Call where origin: T::Origin {
		/// The maximum number of authorized well known nodes
		const MaxWellKnownNodes: u32 = T::MaxWellKnownNodes::get();

		/// The maximum length in bytes of PeerId
		const MaxPeerIdLength: u32 = T::MaxPeerIdLength::get();

		type Error = Error<T>;

		fn deposit_event() = default;

		/// Add a node to the set of well known nodes. If the node is already claimed, the owner
		/// will be updated and keep the existing additional connection unchanged.
		///
		/// May only be called from `T::AddOrigin`.
		///
		/// - `node`: identifier of the node.
		#[weight = (T::WeightInfo::add_well_known_node(), DispatchClass::Operational)]
		pub fn add_well_known_node(origin, node: PeerId, owner: T::AccountId) {
			T::AddOrigin::ensure_origin(origin)?;
			ensure!(node.0.len() < T::MaxPeerIdLength::get() as usize, Error::<T>::PeerIdTooLong);

			let mut nodes = WellKnownNodes::get();
			ensure!(nodes.len() < T::MaxWellKnownNodes::get() as usize, Error::<T>::TooManyNodes);
			ensure!(!nodes.contains(&node), Error::<T>::AlreadyJoined);

			nodes.insert(node.clone());

			WellKnownNodes::put(&nodes);
			<Owners<T>>::insert(&node, &owner);

			Self::deposit_event(RawEvent::NodeAdded(node, owner));
		}

		/// Remove a node from the set of well known nodes. The ownership and additional
		/// connections of the node will also be removed.
		///
		/// May only be called from `T::RemoveOrigin`.
		///
		/// - `node`: identifier of the node.
		#[weight = (T::WeightInfo::remove_well_known_node(), DispatchClass::Operational)]
		pub fn remove_well_known_node(origin, node: PeerId) {
			T::RemoveOrigin::ensure_origin(origin)?;
			ensure!(node.0.len() < T::MaxPeerIdLength::get() as usize, Error::<T>::PeerIdTooLong);

			let mut nodes = WellKnownNodes::get();
			ensure!(nodes.contains(&node), Error::<T>::NotExist);

			nodes.remove(&node);

			WellKnownNodes::put(&nodes);
			<Owners<T>>::remove(&node);
			AdditionalConnections::remove(&node);

			Self::deposit_event(RawEvent::NodeRemoved(node));
		}

		/// Swap a well known node to another. Both the ownership and additional connections
		/// stay untouched.
		///
		/// May only be called from `T::SwapOrigin`.
		///
		/// - `remove`: the node which will be moved out from the list.
		/// - `add`: the node which will be put in the list.
		#[weight = (T::WeightInfo::swap_well_known_node(), DispatchClass::Operational)]
		pub fn swap_well_known_node(origin, remove: PeerId, add: PeerId) {
			T::SwapOrigin::ensure_origin(origin)?;
			ensure!(remove.0.len() < T::MaxPeerIdLength::get() as usize, Error::<T>::PeerIdTooLong);
			ensure!(add.0.len() < T::MaxPeerIdLength::get() as usize, Error::<T>::PeerIdTooLong);

			if remove == add { return Ok(()) }

			let mut nodes = WellKnownNodes::get();
			ensure!(nodes.contains(&remove), Error::<T>::NotExist);
			ensure!(!nodes.contains(&add), Error::<T>::AlreadyJoined);

			nodes.remove(&remove);
			nodes.insert(add.clone());

			WellKnownNodes::put(&nodes);
			Owners::<T>::swap(&remove, &add);
			AdditionalConnections::swap(&remove, &add);

			Self::deposit_event(RawEvent::NodeSwapped(remove, add));
		}

		/// Reset all the well known nodes. This will not remove the ownership and additional
		/// connections for the removed nodes. The node owner can perform further cleaning if
		/// they decide to leave the network.
		///
		/// May only be called from `T::ResetOrigin`.
		///
		/// - `nodes`: the new nodes for the allow list.
		#[weight = (T::WeightInfo::reset_well_known_nodes(), DispatchClass::Operational)]
		pub fn reset_well_known_nodes(origin, nodes: Vec<(PeerId, T::AccountId)>) {
			T::ResetOrigin::ensure_origin(origin)?;
			ensure!(nodes.len() < T::MaxWellKnownNodes::get() as usize, Error::<T>::TooManyNodes);

			Self::initialize_nodes(&nodes);

			Self::deposit_event(RawEvent::NodesReset(nodes));
		}

		/// A given node can be claimed by anyone. The owner should be the first to know its
		/// PeerId, so claim it right away!
		///
		/// - `node`: identifier of the node.
		#[weight = T::WeightInfo::claim_node()]
		pub fn claim_node(origin, node: PeerId) {
			let sender = ensure_signed(origin)?;

			ensure!(node.0.len() < T::MaxPeerIdLength::get() as usize, Error::<T>::PeerIdTooLong);
			ensure!(!Owners::<T>::contains_key(&node),Error::<T>::AlreadyClaimed);

			Owners::<T>::insert(&node, &sender);
			Self::deposit_event(RawEvent::NodeClaimed(node, sender));
		}

		/// A claim can be removed by its owner and get back the reservation. The additional
		/// connections are also removed. You can't remove a claim on well known nodes, as it
		/// needs to reach consensus among the network participants.
		///
		/// - `node`: identifier of the node.
		#[weight = T::WeightInfo::remove_claim()]
		pub fn remove_claim(origin, node: PeerId) {
			let sender = ensure_signed(origin)?;

			ensure!(node.0.len() < T::MaxPeerIdLength::get() as usize, Error::<T>::PeerIdTooLong);
			ensure!(Owners::<T>::contains_key(&node), Error::<T>::NotClaimed);
			ensure!(Owners::<T>::get(&node) == sender, Error::<T>::NotOwner);
			ensure!(!WellKnownNodes::get().contains(&node), Error::<T>::PermissionDenied);

			Owners::<T>::remove(&node);
			AdditionalConnections::remove(&node);

			Self::deposit_event(RawEvent::ClaimRemoved(node, sender));
		}

		/// A node can be transferred to a new owner.
		///
		/// - `node`: identifier of the node.
		/// - `owner`: new owner of the node.
		#[weight = T::WeightInfo::transfer_node()]
		pub fn transfer_node(origin, node: PeerId, owner: T::AccountId) {
			let sender = ensure_signed(origin)?;

			ensure!(node.0.len() < T::MaxPeerIdLength::get() as usize, Error::<T>::PeerIdTooLong);
			ensure!(Owners::<T>::contains_key(&node), Error::<T>::NotClaimed);
			ensure!(Owners::<T>::get(&node) == sender, Error::<T>::NotOwner);

			Owners::<T>::insert(&node, &owner);

			Self::deposit_event(RawEvent::NodeTransferred(node, owner));
		}

		/// Add additional connections to a given node.
		///
		/// - `node`: identifier of the node.
		/// - `connections`: additonal nodes from which the connections are allowed.
		#[weight = T::WeightInfo::add_connections()]
		pub fn add_connections(
			origin,
			node: PeerId,
			connections: Vec<PeerId>
		) {
			let sender = ensure_signed(origin)?;

			ensure!(node.0.len() < T::MaxPeerIdLength::get() as usize, Error::<T>::PeerIdTooLong);
			ensure!(Owners::<T>::contains_key(&node), Error::<T>::NotClaimed);
			ensure!(Owners::<T>::get(&node) == sender, Error::<T>::NotOwner);

			let mut nodes = AdditionalConnections::get(&node);

			for add_node in connections.iter() {
				if *add_node == node {
					continue;
				}
				nodes.insert(add_node.clone());
			}

			AdditionalConnections::insert(&node, nodes);

			Self::deposit_event(RawEvent::ConnectionsAdded(node, connections));
		}

		/// Remove additional connections of a given node.
		///
		/// - `node`: identifier of the node.
		/// - `connections`: additonal nodes from which the connections are not allowed anymore.
		#[weight = T::WeightInfo::remove_connections()]
		pub fn remove_connections(
			origin,
			node: PeerId,
			connections: Vec<PeerId>
		) {
			let sender = ensure_signed(origin)?;

			ensure!(node.0.len() < T::MaxPeerIdLength::get() as usize, Error::<T>::PeerIdTooLong);
			ensure!(Owners::<T>::contains_key(&node), Error::<T>::NotClaimed);
			ensure!(Owners::<T>::get(&node) == sender, Error::<T>::NotOwner);

			let mut nodes = AdditionalConnections::get(&node);

			for remove_node in connections.iter() {
				nodes.remove(remove_node);
			}

			AdditionalConnections::insert(&node, nodes);

			Self::deposit_event(RawEvent::ConnectionsRemoved(node, connections));
		}

		/// Set reserved node every block. It may not be enabled depends on the offchain
		/// worker settings when starting the node.
		fn offchain_worker(now: T::BlockNumber) {
			let network_state = sp_io::offchain::network_state();
			match network_state {
				Err(_) => debug::error!("Error: failed to get network state of node at {:?}", now),
				Ok(state) => {
					let encoded_peer = state.peer_id.0;
					match Decode::decode(&mut &encoded_peer[..]) {
						Err(_) => debug::error!("Error: failed to decode PeerId at {:?}", now),
						Ok(node) => sp_io::offchain::set_authorized_nodes(
							Self::get_authorized_nodes(&PeerId(node)),
							true
						)
					}
				}
			}
		}
	}
}

impl<T: Config> Module<T> {
	fn initialize_nodes(nodes: &Vec<(PeerId, T::AccountId)>) {
		let peer_ids = nodes.iter()
			.map(|item| item.0.clone())
			.collect::<BTreeSet<PeerId>>();
		WellKnownNodes::put(&peer_ids);

		for (node, who) in nodes.iter() {
			Owners::<T>::insert(node, who);
		}
	}

	fn get_authorized_nodes(node: &PeerId) -> Vec<PeerId> {
		let mut nodes = AdditionalConnections::get(node);

		let mut well_known_nodes = WellKnownNodes::get();
		if well_known_nodes.contains(node) {
			well_known_nodes.remove(node);
			nodes.extend(well_known_nodes);
		}

		Vec::from_iter(nodes)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate as pallet_node_authorization;

	use frame_support::{assert_ok, assert_noop, parameter_types, ord_parameter_types};
	use frame_system::EnsureSignedBy;
	use sp_core::H256;
	use sp_runtime::{traits::{BlakeTwo256, IdentityLookup, BadOrigin}, testing::Header};

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
	type Block = frame_system::mocking::MockBlock<Test>;

	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system::{Module, Call, Config, Storage, Event<T>},
			NodeAuthorization: pallet_node_authorization::{
				Module, Call, Storage, Config<T>, Event<T>,
			},
		}
	);

	parameter_types! {
		pub const BlockHashCount: u64 = 250;
	}
	impl frame_system::Config for Test {
		type BaseCallFilter = ();
		type DbWeight = ();
		type BlockWeights = ();
		type BlockLength = ();
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = Call;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = Event;
		type BlockHashCount = BlockHashCount;
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
	}

	ord_parameter_types! {
		pub const One: u64 = 1;
		pub const Two: u64 = 2;
		pub const Three: u64 = 3;
		pub const Four: u64 = 4;
	}
	parameter_types! {
		pub const MaxWellKnownNodes: u32 = 4;
		pub const MaxPeerIdLength: u32 = 2;
	}
	impl Config for Test {
		type Event = Event;
		type MaxWellKnownNodes = MaxWellKnownNodes;
		type MaxPeerIdLength = MaxPeerIdLength;
		type AddOrigin = EnsureSignedBy<One, u64>;
		type RemoveOrigin = EnsureSignedBy<Two, u64>;
		type SwapOrigin = EnsureSignedBy<Three, u64>;
		type ResetOrigin = EnsureSignedBy<Four, u64>;
		type WeightInfo = ();
	}

	fn test_node(id: u8) -> PeerId {
		PeerId(vec![id])
	}

	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_node_authorization::GenesisConfig::<Test> {
			nodes: vec![(test_node(10), 10), (test_node(20), 20), (test_node(30), 30)],
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn add_well_known_node_works() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				NodeAuthorization::add_well_known_node(Origin::signed(2), test_node(15), 15),
				BadOrigin
			);
			assert_noop!(
				NodeAuthorization::add_well_known_node(Origin::signed(1), PeerId(vec![1, 2, 3]), 15),
				Error::<Test>::PeerIdTooLong
			);
			assert_noop!(
				NodeAuthorization::add_well_known_node(Origin::signed(1), test_node(20), 20),
				Error::<Test>::AlreadyJoined
			);

			assert_ok!(
				NodeAuthorization::add_well_known_node(Origin::signed(1), test_node(15), 15)
			);
			assert_eq!(
				WellKnownNodes::get(),
				BTreeSet::from_iter(vec![test_node(10), test_node(15), test_node(20), test_node(30)])
			);
			assert_eq!(Owners::<Test>::get(test_node(10)), 10);
			assert_eq!(Owners::<Test>::get(test_node(20)), 20);
			assert_eq!(Owners::<Test>::get(test_node(30)), 30);
			assert_eq!(Owners::<Test>::get(test_node(15)), 15);

			assert_noop!(
				NodeAuthorization::add_well_known_node(Origin::signed(1), test_node(25), 25),
				Error::<Test>::TooManyNodes
			);
		});
	}

	#[test]
	fn remove_well_known_node_works() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				NodeAuthorization::remove_well_known_node(Origin::signed(3), test_node(20)),
				BadOrigin
			);
			assert_noop!(
				NodeAuthorization::remove_well_known_node(Origin::signed(2), PeerId(vec![1, 2, 3])),
				Error::<Test>::PeerIdTooLong
			);
			assert_noop!(
				NodeAuthorization::remove_well_known_node(Origin::signed(2), test_node(40)),
				Error::<Test>::NotExist
			);

			AdditionalConnections::insert(
				test_node(20),
				BTreeSet::from_iter(vec![test_node(40)])
			);
			assert!(AdditionalConnections::contains_key(test_node(20)));

			assert_ok!(
				NodeAuthorization::remove_well_known_node(Origin::signed(2), test_node(20))
			);
			assert_eq!(
				WellKnownNodes::get(),
				BTreeSet::from_iter(vec![test_node(10), test_node(30)])
			);
			assert!(!Owners::<Test>::contains_key(test_node(20)));
			assert!(!AdditionalConnections::contains_key(test_node(20)));
		});
	}

	#[test]
	fn swap_well_known_node_works() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				NodeAuthorization::swap_well_known_node(
					Origin::signed(4), test_node(20), test_node(5)
				),
				BadOrigin
			);
			assert_noop!(
				NodeAuthorization::swap_well_known_node(
					Origin::signed(3), PeerId(vec![1, 2, 3]), test_node(20)
				),
				Error::<Test>::PeerIdTooLong
			);
			assert_noop!(
				NodeAuthorization::swap_well_known_node(
					Origin::signed(3), test_node(20), PeerId(vec![1, 2, 3])
				),
				Error::<Test>::PeerIdTooLong
			);

			assert_ok!(
				NodeAuthorization::swap_well_known_node(
					Origin::signed(3), test_node(20), test_node(20)
				)
			);
			assert_eq!(
				WellKnownNodes::get(),
				BTreeSet::from_iter(vec![test_node(10), test_node(20), test_node(30)])
			);

			assert_noop!(
				NodeAuthorization::swap_well_known_node(
					Origin::signed(3), test_node(15), test_node(5)
				),
				Error::<Test>::NotExist
			);
			assert_noop!(
				NodeAuthorization::swap_well_known_node(
					Origin::signed(3), test_node(20), test_node(30)
				),
				Error::<Test>::AlreadyJoined
			);

			AdditionalConnections::insert(
				test_node(20),
				BTreeSet::from_iter(vec![test_node(15)])
			);
			assert_ok!(
				NodeAuthorization::swap_well_known_node(
					Origin::signed(3), test_node(20), test_node(5)
				)
			);
			assert_eq!(
				WellKnownNodes::get(),
				BTreeSet::from_iter(vec![test_node(5), test_node(10), test_node(30)])
			);
			assert!(!Owners::<Test>::contains_key(test_node(20)));
			assert_eq!(Owners::<Test>::get(test_node(5)), 20);
			assert!(!AdditionalConnections::contains_key(test_node(20)));
			assert_eq!(
				AdditionalConnections::get(test_node(5)),
				BTreeSet::from_iter(vec![test_node(15)])
			);
		});
	}

	#[test]
	fn reset_well_known_nodes_works() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				NodeAuthorization::reset_well_known_nodes(
					Origin::signed(3),
					vec![(test_node(15), 15), (test_node(5), 5), (test_node(20), 20)]
				),
				BadOrigin
			);
			assert_noop!(
				NodeAuthorization::reset_well_known_nodes(
					Origin::signed(4),
					vec![
						(test_node(15), 15),
						(test_node(5), 5),
						(test_node(20), 20),
						(test_node(25), 25),
					]
				),
				Error::<Test>::TooManyNodes
			);

			assert_ok!(
				NodeAuthorization::reset_well_known_nodes(
					Origin::signed(4),
					vec![(test_node(15), 15), (test_node(5), 5), (test_node(20), 20)]
				)
			);
			assert_eq!(
				WellKnownNodes::get(),
				BTreeSet::from_iter(vec![test_node(5), test_node(15), test_node(20)])
			);
			assert_eq!(Owners::<Test>::get(test_node(5)), 5);
			assert_eq!(Owners::<Test>::get(test_node(15)), 15);
			assert_eq!(Owners::<Test>::get(test_node(20)), 20);
		});
	}

	#[test]
	fn claim_node_works() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				NodeAuthorization::claim_node(Origin::signed(1), PeerId(vec![1, 2, 3])),
				Error::<Test>::PeerIdTooLong
			);
			assert_noop!(
				NodeAuthorization::claim_node(Origin::signed(1), test_node(20)),
				Error::<Test>::AlreadyClaimed
			);

			assert_ok!(NodeAuthorization::claim_node(Origin::signed(15), test_node(15)));
			assert_eq!(Owners::<Test>::get(test_node(15)), 15);
		});
	}

	#[test]
	fn remove_claim_works() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				NodeAuthorization::remove_claim(Origin::signed(15), PeerId(vec![1, 2, 3])),
				Error::<Test>::PeerIdTooLong
			);
			assert_noop!(
				NodeAuthorization::remove_claim(Origin::signed(15), test_node(15)),
				Error::<Test>::NotClaimed
			);

			assert_noop!(
				NodeAuthorization::remove_claim(Origin::signed(15), test_node(20)),
				Error::<Test>::NotOwner
			);

			assert_noop!(
				NodeAuthorization::remove_claim(Origin::signed(20), test_node(20)),
				Error::<Test>::PermissionDenied
			);

			Owners::<Test>::insert(test_node(15), 15);
			AdditionalConnections::insert(
				test_node(15),
				BTreeSet::from_iter(vec![test_node(20)])
			);
			assert_ok!(NodeAuthorization::remove_claim(Origin::signed(15), test_node(15)));
			assert!(!Owners::<Test>::contains_key(test_node(15)));
			assert!(!AdditionalConnections::contains_key(test_node(15)));
		});
	}

	#[test]
	fn transfer_node_works() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				NodeAuthorization::transfer_node(Origin::signed(15), PeerId(vec![1, 2, 3]), 10),
				Error::<Test>::PeerIdTooLong
			);
			assert_noop!(
				NodeAuthorization::transfer_node(Origin::signed(15), test_node(15), 10),
				Error::<Test>::NotClaimed
			);

			assert_noop!(
				NodeAuthorization::transfer_node(Origin::signed(15), test_node(20), 10),
				Error::<Test>::NotOwner
			);

			assert_ok!(NodeAuthorization::transfer_node(Origin::signed(20), test_node(20), 15));
			assert_eq!(Owners::<Test>::get(test_node(20)), 15);
		});
	}

	#[test]
	fn add_connections_works() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				NodeAuthorization::add_connections(
					Origin::signed(15), PeerId(vec![1, 2, 3]), vec![test_node(5)]
				),
				Error::<Test>::PeerIdTooLong
			);
			assert_noop!(
				NodeAuthorization::add_connections(
					Origin::signed(15), test_node(15), vec![test_node(5)]
				),
				Error::<Test>::NotClaimed
			);

			assert_noop!(
				NodeAuthorization::add_connections(
					Origin::signed(15), test_node(20), vec![test_node(5)]
				),
				Error::<Test>::NotOwner
			);

			assert_ok!(
				NodeAuthorization::add_connections(
					Origin::signed(20),
					test_node(20),
					vec![test_node(15), test_node(5), test_node(25), test_node(20)]
				)
			);
			assert_eq!(
				AdditionalConnections::get(test_node(20)),
				BTreeSet::from_iter(vec![test_node(5), test_node(15), test_node(25)])
			);
		});
	}

	#[test]
	fn remove_connections_works() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				NodeAuthorization::remove_connections(
					Origin::signed(15), PeerId(vec![1, 2, 3]), vec![test_node(5)]
				),
				Error::<Test>::PeerIdTooLong
			);
			assert_noop!(
				NodeAuthorization::remove_connections(
					Origin::signed(15), test_node(15), vec![test_node(5)]
				),
				Error::<Test>::NotClaimed
			);

			assert_noop!(
				NodeAuthorization::remove_connections(
					Origin::signed(15), test_node(20), vec![test_node(5)]
				),
				Error::<Test>::NotOwner
			);

			AdditionalConnections::insert(
				test_node(20),
				BTreeSet::from_iter(vec![test_node(5), test_node(15), test_node(25)])
			);
			assert_ok!(
				NodeAuthorization::remove_connections(
					Origin::signed(20),
					test_node(20),
					vec![test_node(15), test_node(5)]
				)
			);
			assert_eq!(
				AdditionalConnections::get(test_node(20)),
				BTreeSet::from_iter(vec![test_node(25)])
			);
		});
	}

	#[test]
	fn get_authorized_nodes_works() {
		new_test_ext().execute_with(|| {
			AdditionalConnections::insert(
				test_node(20),
				BTreeSet::from_iter(vec![test_node(5), test_node(15), test_node(25)])
			);

			let mut authorized_nodes = Module::<Test>::get_authorized_nodes(&test_node(20));
			authorized_nodes.sort();
			assert_eq!(
				authorized_nodes,
				vec![test_node(5), test_node(10), test_node(15), test_node(25), test_node(30)]
			);
		});
	}
}
