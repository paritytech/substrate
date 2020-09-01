// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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
//! It provides two ways to authorize a node,
//!
//! - a set of well known nodes across different organizations in which the
//! connections are allowed.
//! - users can claim the ownership for each node, then manage the connections of
//! the node.
//!
//! A node must have an owner. The owner can additionally change the connections
//! for the node. Only one user is allowed to claim a specific node. To eliminate
//! false claim, the maintainer of the node should claim it before even starting the
//! node. This pallet use offchain work to set reserved nodes, if the node is not
//! an authority, make sure to enable offchain worker with the right CLI flag.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use sp_core::NodePublicKey;
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

pub trait Trait: frame_system::Trait {
    /// The event type of this module.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

    /// The maximum number of well known nodes that are allowed to set
    type MaxWellKnownNodes: Get<u32>;

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
    trait Store for Module<T: Trait> as NodeAuthorization {
        /// The set of well known nodes. This is stored sorted (just by value).
        pub WellKnownNodes get(fn well_known_nodes): Vec<NodePublicKey>;
        /// A map that maintains the ownership of each node.
        pub Owners get(fn owners):
            map hasher(blake2_128_concat) NodePublicKey => T::AccountId;
        /// The additional adapative connections of each node.
        pub AdditionalConnections get(fn additional_connection):
            map hasher(blake2_128_concat) NodePublicKey => Vec<NodePublicKey>;
    }
    add_extra_genesis {
        config(nodes): Vec<(NodePublicKey, T::AccountId)>;
        build(|config: &GenesisConfig<T>| {
            <Module<T>>::initialize_nodes(&config.nodes)
        })
    }
}

decl_event! {
    pub enum Event<T> where
        <T as frame_system::Trait>::AccountId,
    {
        /// The given well known node was added.
        NodeAdded(NodePublicKey, AccountId),
        /// The given well known node was removed.
        NodeRemoved(NodePublicKey),
        /// The given well known node was swapped; first item was removed,
        /// the latter was added.
        NodeSwapped(NodePublicKey, NodePublicKey),
        /// The given well known nodes were reset.
        NodesReset(Vec<(NodePublicKey, AccountId)>),
        /// The given node was claimed by a user.
        NodeClaimed(NodePublicKey, AccountId),
        /// The given claim was removed by its owner.
        ClaimRemoved(NodePublicKey, AccountId),
        /// The node was transferred to another account.
        NodeTransferred(NodePublicKey, AccountId, AccountId),
        /// The allowed connections were added to a node.
        ConnectionsAdded(NodePublicKey, Vec<NodePublicKey>),
        /// The allowed connections were removed from a node.
        ConnectionsRemoved(NodePublicKey, Vec<NodePublicKey>),
    }
}

decl_error! {
    /// Error for the node authorization module.
    pub enum Error for Module<T: Trait> {
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
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {
        /// The maximum number of authorized well known nodes
        const MaxWellKnownNodes: u32 = T::MaxWellKnownNodes::get();

        type Error = Error<T>;

        fn deposit_event() = default;

        /// Add a node to the set of well known nodes. If the node is already claimed, the owner
        /// will be updated and keep the existing additional connection unchanged.
        ///
        /// May only be called from `T::AddOrigin`.
        ///
        /// - `node`: identifier of the node.
        #[weight = (T::WeightInfo::add_well_known_node(), DispatchClass::Operational)]
        pub fn add_well_known_node(origin, node: NodePublicKey, owner: T::AccountId) {
            T::AddOrigin::ensure_origin(origin)?;

            let mut nodes = WellKnownNodes::get();
            ensure!(nodes.len() < T::MaxWellKnownNodes::get() as usize, Error::<T>::TooManyNodes);

            let location = nodes.binary_search(&node).err().ok_or(Error::<T>::AlreadyJoined)?;
            nodes.insert(location, node.clone());
            
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
        pub fn remove_well_known_node(origin, node: NodePublicKey) {
            T::RemoveOrigin::ensure_origin(origin)?;

            let mut nodes = WellKnownNodes::get();

            let location = nodes.binary_search(&node).ok().ok_or(Error::<T>::NotExist)?;
            nodes.remove(location);
            
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
        pub fn swap_well_known_node(origin, remove: NodePublicKey, add: NodePublicKey) {
            T::SwapOrigin::ensure_origin(origin)?;

            if remove == add { return Ok(()) }
            
            let mut nodes = WellKnownNodes::get();
            let remove_location = nodes.binary_search(&remove).ok().ok_or(Error::<T>::NotExist)?;
            nodes.remove(remove_location);
            let add_location = nodes.binary_search(&add).err().ok_or(Error::<T>::AlreadyJoined)?;
            nodes.insert(add_location, add.clone());
            
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
        pub fn reset_well_known_nodes(origin, nodes: Vec<(NodePublicKey, T::AccountId)>) {
            T::ResetOrigin::ensure_origin(origin)?;
            ensure!(nodes.len() < T::MaxWellKnownNodes::get() as usize, Error::<T>::TooManyNodes);

            Self::initialize_nodes(&nodes);

            Self::deposit_event(RawEvent::NodesReset(nodes));
        }

        /// A given node can be claimed by anyone. The owner should be the first to know its   
        /// public key, so claim it right away!
        ///
        /// - `node`: identifier of the node.
        #[weight = T::WeightInfo::claim_node()]
        pub fn claim_node(origin, node: NodePublicKey) {
            let sender = ensure_signed(origin)?;
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
        pub fn remove_claim(origin, node: NodePublicKey) {
            let sender = ensure_signed(origin)?;
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
        pub fn transfer_node(origin, node: NodePublicKey, owner: T::AccountId) {
            let sender = ensure_signed(origin)?;
            ensure!(Owners::<T>::contains_key(&node), Error::<T>::NotClaimed);
            ensure!(Owners::<T>::get(&node) == sender, Error::<T>::NotOwner);

            Owners::<T>::insert(&node, &owner);

            Self::deposit_event(RawEvent::NodeTransferred(node, sender, owner));
        }

        /// Add additional connections to a given node.
        ///
        /// - `node`: identifier of the node.
        /// - `connections`: additonal nodes from which the connections are allowed.
        #[weight = T::WeightInfo::add_connections()]
        pub fn add_connections(
            origin,
            node: NodePublicKey,
            connections: Vec<NodePublicKey>
        ) {
            let sender = ensure_signed(origin)?;
            ensure!(Owners::<T>::contains_key(&node), Error::<T>::NotClaimed);
            ensure!(Owners::<T>::get(&node) == sender, Error::<T>::NotOwner);

            let mut nodes = AdditionalConnections::get(&node);

            for add_node in connections.iter() {
                if *add_node == node {
                    continue;
                }
                if let Err(add_location) = nodes.binary_search(add_node) {
                    nodes.insert(add_location, add_node.clone());
                }
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
            node: NodePublicKey,
            connections: Vec<NodePublicKey>
        ) {
            let sender = ensure_signed(origin)?;
            ensure!(Owners::<T>::contains_key(&node), Error::<T>::NotClaimed);
            ensure!(Owners::<T>::get(&node) == sender, Error::<T>::NotOwner);

            let mut nodes = AdditionalConnections::get(&node);

            for remove_node in connections.iter() {
                if let Ok(remove_location) = nodes.binary_search(remove_node) {
                    nodes.remove(remove_location);
                }
            }
            
            AdditionalConnections::insert(&node, nodes);

            Self::deposit_event(RawEvent::ConnectionsRemoved(node, connections));
        }

        /// Set reserved node every block. If may not be enabled depends on the offchain
        /// worker CLI flag.
        fn offchain_worker(now: T::BlockNumber) {
            let node_public_key = sp_io::offchain::get_node_public_key();
            match node_public_key {
                Err(_) => debug::error!("Error: failed to get public key of node at {:?}", now),
                Ok(node) => sp_io::offchain::set_reserved_nodes(
                    Self::get_authorized_nodes(&node), true
                ),
            }
        }
    }
}

impl<T: Trait> Module<T> {
    fn initialize_nodes(nodes: &Vec<(NodePublicKey, T::AccountId)>) {
        let mut node_public_keys = nodes.iter()
            .map(|item| item.0.clone())
            .collect::<Vec<NodePublicKey>>();
        node_public_keys.sort();
        WellKnownNodes::put(&node_public_keys);

        for (node, who) in nodes.iter() {
            Owners::<T>::insert(node, who);
        }
    }

    fn get_authorized_nodes(node: &NodePublicKey) -> Vec<NodePublicKey> {
        let mut nodes = AdditionalConnections::get(node);
        
        let mut well_known_nodes = WellKnownNodes::get();
        if let Ok(location) = well_known_nodes.binary_search(node) {
            well_known_nodes.remove(location);
            nodes.extend(well_known_nodes);
        }

        nodes
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use frame_support::{
        assert_ok, assert_noop, impl_outer_origin, weights::Weight,
        parameter_types, ord_parameter_types,
    };
    use frame_system::EnsureSignedBy;
    use sp_core::{H256, ed25519::Public};
    use sp_runtime::{Perbill, traits::{BlakeTwo256, IdentityLookup, BadOrigin}, testing::Header};

    impl_outer_origin! {
        pub enum Origin for Test where system = frame_system {}
    }

    #[derive(Clone, Eq, PartialEq)]
    pub struct Test;

    parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
    }
    impl frame_system::Trait for Test {
		type BaseCallFilter = ();
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = ();
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type DbWeight = ();
		type BlockExecutionWeight = ();
		type ExtrinsicBaseWeight = ();
		type MaximumExtrinsicWeight = MaximumBlockWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
		type ModuleToIndex = ();
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
        type SystemWeightInfo = ();
    }
    
    ord_parameter_types! {
		pub const One: u64 = 1;
		pub const Two: u64 = 2;
		pub const Three: u64 = 3;
        pub const Four: u64 = 4;
    }
    parameter_types! {
        pub const MaxWellKnownNodes: u32 = 4;
    }
    impl Trait for Test {
        type Event = ();
        type MaxWellKnownNodes = MaxWellKnownNodes;
        type AddOrigin = EnsureSignedBy<One, u64>;
        type RemoveOrigin = EnsureSignedBy<Two, u64>;
        type SwapOrigin = EnsureSignedBy<Three, u64>;
        type ResetOrigin = EnsureSignedBy<Four, u64>;
        type WeightInfo = ();
    }
    
    type NodeAuthorization = Module<Test>;

    fn test_node(id: u8) -> NodePublicKey {
        let mut arr = [0u8; 32];
        arr[31] = id;
        NodePublicKey::Ed25519(Public::from_raw(arr))
    }

    fn new_test_ext() -> sp_io::TestExternalities {
        let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
        GenesisConfig::<Test> {
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
                NodeAuthorization::add_well_known_node(Origin::signed(1), test_node(20), 20),
                Error::<Test>::AlreadyJoined
            );
            
            assert_ok!(
                NodeAuthorization::add_well_known_node(Origin::signed(1), test_node(15), 15)
            );
            assert_eq!(
                WellKnownNodes::get(),
                vec![test_node(10), test_node(15), test_node(20), test_node(30)]
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
                NodeAuthorization::remove_well_known_node(Origin::signed(2), test_node(40)),
                Error::<Test>::NotExist
            );
            
            AdditionalConnections::insert(test_node(20), vec![test_node(40)]);
            assert!(AdditionalConnections::contains_key(test_node(20)));

            assert_ok!(
                NodeAuthorization::remove_well_known_node(Origin::signed(2), test_node(20))
            );
            assert_eq!(WellKnownNodes::get(), vec![test_node(10), test_node(30)]);
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
            
            assert_ok!(
                NodeAuthorization::swap_well_known_node(
                    Origin::signed(3), test_node(20), test_node(20)
                )
            );
            assert_eq!(
                WellKnownNodes::get(),
                vec![test_node(10), test_node(20), test_node(30)]
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
            
            AdditionalConnections::insert(test_node(20), vec![test_node(15)]);
            assert_ok!(
                NodeAuthorization::swap_well_known_node(
                    Origin::signed(3), test_node(20), test_node(5)
                )
            );
            assert_eq!(
                WellKnownNodes::get(),
                vec![test_node(5), test_node(10), test_node(30)]
            );
            assert!(!Owners::<Test>::contains_key(test_node(20)));
            assert_eq!(Owners::<Test>::get(test_node(5)), 20);
            assert!(!AdditionalConnections::contains_key(test_node(20)));
            assert_eq!(AdditionalConnections::get(test_node(5)), vec![test_node(15)]);
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
                vec![test_node(5), test_node(15), test_node(20)]
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
            AdditionalConnections::insert(test_node(15), vec![test_node(20)]);
            assert_ok!(NodeAuthorization::remove_claim(Origin::signed(15), test_node(15)));
            assert!(!Owners::<Test>::contains_key(test_node(15)));
            assert!(!AdditionalConnections::contains_key(test_node(15)));
        });
    }

    #[test]
    fn transfer_node_works() {
        new_test_ext().execute_with(|| {
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
                vec![test_node(5), test_node(15), test_node(25)]
            );
        });
    }

    #[test]
    fn remove_connections_works() {
        new_test_ext().execute_with(|| {
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
                test_node(20), vec![test_node(5), test_node(15), test_node(25)]
            );
            assert_ok!(
                NodeAuthorization::remove_connections(
                    Origin::signed(20),
                    test_node(20),
                    vec![test_node(15), test_node(5)]
                )
            );
            assert_eq!(AdditionalConnections::get(test_node(20)), vec![test_node(25)]);
        });
    }

    #[test]
    fn get_authorize_nodes_worker() {
        new_test_ext().execute_with(|| {
            AdditionalConnections::insert(
                test_node(20), vec![test_node(5), test_node(15), test_node(25)]
            );
            assert_eq!(
                Module::<Test>::get_authorized_nodes(&test_node(20)),
                vec![test_node(5), test_node(15), test_node(25), test_node(10), test_node(30)]
            );
        });
    }
}
