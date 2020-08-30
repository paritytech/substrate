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
//! * a set of well known nodes across different organizations in which
//! the connections are allowed.
//! * users can claim the ownership for each node, then manage the connection of the node.
//!
//! A node must have an owner. The owner can make additional adaptive change for
//! the connection of the node. Only one user can `claim` a specific node.
//! To eliminate false claim, the maintainer of the node should claim it before
//! even start the node.

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
}

impl WeightInfo for () {
    fn add_well_known_node() -> Weight { 50_000_000 }
    fn remove_well_known_node() -> Weight { 50_000_000 }
    fn swap_well_known_node() -> Weight { 50_000_000 }
    fn reset_well_known_nodes() -> Weight { 50_000_000 }
    fn claim_node() -> Weight { 50_000_000 }
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
        /// The additional adapative connections of a node.
        pub AdditionalConnections get(fn additional_connection):
            map hasher(blake2_128_concat) NodePublicKey => Vec<NodePublicKey>;
    }
    add_extra_genesis {
        config(nodes): Vec<(NodePublicKey, T::AccountId)>;
        build(|config: &GenesisConfig<T>| {
            WellKnownNodes::put(
                config.nodes.iter()
                    .map(|item| item.0.clone())
                    .collect::<Vec<NodePublicKey>>()
            );
            for (node, who) in config.nodes.iter() {
                Owners::<T>::insert(node, who);
			}
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
        /// Two given well known node were swapped; first item is removed,
        /// the latter is added.
        NodeSwapped(NodePublicKey, NodePublicKey),
        /// The given well known nodes were reset.
        NodesReset(Vec<(NodePublicKey, AccountId)>),
        /// The given node was claimed by a user.
        NodeClaimed(NodePublicKey, AccountId),
        /// New connections were added to a node.
        ConnectionsAdded(NodePublicKey, Vec<NodePublicKey>),
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

        /// Swap one well know node to another. Both the ownership and additonal connections
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

            Self::deposit_event(RawEvent::NodeSwapped(remove, add));
        }
        
        /// Reset all the well known nodes. This will not remove the ownership and additional
        /// connections for the removed nodes. The node owner can perform furthur cleaning if
        /// they decide to leave the network.
        ///
        /// May only be called from `T::ResetOrigin`.
        ///
        /// - `nodes`: the new nodes for the allow list.
        #[weight = (T::WeightInfo::reset_well_known_nodes(), DispatchClass::Operational)]
        pub fn reset_well_known_nodes(origin, nodes: Vec<(NodePublicKey, T::AccountId)>) {
            T::ResetOrigin::ensure_origin(origin)?;
            ensure!(nodes.len() < T::MaxWellKnownNodes::get() as usize, Error::<T>::TooManyNodes);

            Self::initialize_nodes(nodes.clone());

            Self::deposit_event(RawEvent::NodesReset(nodes));
        }

        /// Send a transaction to claim the node.
        ///
        /// - `node_public_key`: identifier of the node.
        #[weight = T::WeightInfo::claim_node()]
        pub fn claim_node(origin, node_public_key: NodePublicKey) {
            let sender = ensure_signed(origin)?;

            ensure!(
                !Owners::<T>::contains_key(&node_public_key),
                Error::<T>::AlreadyClaimed
            );

            Owners::<T>::insert(&node_public_key, &sender);
            Self::deposit_event(RawEvent::NodeClaimed(node_public_key, sender));
        }

        /// Send a transaction to claim the node.
        ///
        /// - `node_public_key`: identifier of the node.
        #[weight = T::WeightInfo::claim_node()]
        pub fn add_connection(
            origin,
            node_public_key: NodePublicKey,
            connections: Vec<NodePublicKey>
        ) {
            let sender = ensure_signed(origin)?;

            ensure!(
                Owners::<T>::contains_key(&node_public_key),
                Error::<T>::NotClaimed
            );

            ensure!(
                Owners::<T>::get(&node_public_key) == sender,
                Error::<T>::NotOwner
            );

            let mut nodes = AdditionalConnections::get(&node_public_key);
            nodes.extend(connections.clone());
            nodes.sort();
            nodes.dedup();
            
            AdditionalConnections::insert(&node_public_key, nodes);

            Self::deposit_event(RawEvent::ConnectionsAdded(node_public_key, connections));
        }

        fn offchain_worker(now: T::BlockNumber) {
            let node_public_key = sp_io::offchain::get_node_public_key();
            match node_public_key {
                Err(_) => debug::error!("Error: failed to get public key of node at {:?}", now),
                Ok(node) => Self::authorize_nodes(node),
            }
        }
    }
}

impl<T: Trait> Module<T> {
    fn initialize_nodes(nodes: Vec<(NodePublicKey, T::AccountId)>) {
        let mut node_public_keys = nodes.iter()
            .map(|item| item.0.clone())
            .collect::<Vec<NodePublicKey>>();
        node_public_keys.sort();
        WellKnownNodes::put(&node_public_keys);

        for (node, who) in nodes.iter() {
            Owners::<T>::insert(node, who);
        }
    }

    fn authorize_nodes(node: NodePublicKey) {
        let mut nodes = AdditionalConnections::get(&node);
        
        let well_known_nodes = WellKnownNodes::get();
        if well_known_nodes.binary_search(&node).is_ok() {
            nodes.extend(well_known_nodes);
        }

        sp_io::offchain::set_reserved_nodes(nodes, true)
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     use frame_support::{
//         assert_ok, assert_noop, impl_outer_origin, weights::Weight,
//         parameter_types, ord_parameter_types,
//     };
//     use frame_system::EnsureSignedBy;
//     use sp_core::{H256, ed25519::Public};
//     use sp_runtime::{Perbill, traits::{BlakeTwo256, IdentityLookup, BadOrigin}, testing::Header};
//     use hex_literal::hex;

//     impl_outer_origin! {
//         pub enum Origin for Test where system = frame_system {}
//     }

//     #[derive(Clone, Eq, PartialEq)]
//     pub struct Test;

//     parameter_types! {
// 		pub const BlockHashCount: u64 = 250;
// 		pub const MaximumBlockWeight: Weight = 1024;
// 		pub const MaximumBlockLength: u32 = 2 * 1024;
// 		pub const AvailableBlockRatio: Perbill = Perbill::one();
// 	}
// 	impl frame_system::Trait for Test {
// 		type BaseCallFilter = ();
// 		type Origin = Origin;
// 		type Index = u64;
// 		type BlockNumber = u64;
// 		type Hash = H256;
// 		type Call = ();
// 		type Hashing = BlakeTwo256;
// 		type AccountId = u64;
// 		type Lookup = IdentityLookup<Self::AccountId>;
// 		type Header = Header;
// 		type Event = ();
// 		type BlockHashCount = BlockHashCount;
// 		type MaximumBlockWeight = MaximumBlockWeight;
// 		type DbWeight = ();
// 		type BlockExecutionWeight = ();
// 		type ExtrinsicBaseWeight = ();
// 		type MaximumExtrinsicWeight = MaximumBlockWeight;
// 		type MaximumBlockLength = MaximumBlockLength;
// 		type AvailableBlockRatio = AvailableBlockRatio;
// 		type Version = ();
// 		type ModuleToIndex = ();
// 		type AccountData = ();
// 		type OnNewAccount = ();
// 		type OnKilledAccount = ();
// 		type SystemWeightInfo = ();
// 	}

//     ord_parameter_types! {
// 		pub const One: u64 = 1;
// 		pub const Two: u64 = 2;
// 		pub const Three: u64 = 3;
// 		pub const Four: u64 = 4;
// 	}
//     parameter_types! {
//         pub const MaxWellKnownNodes: u32 = 4;
//     }
//     impl Trait for Test {
//         type Event = ();
//         type MaxWellKnownNodes = MaxWellKnownNodes;
//         type AddOrigin = EnsureSignedBy<One, u64>;
//         type RemoveOrigin = EnsureSignedBy<Two, u64>;
//         type SwapOrigin = EnsureSignedBy<Three, u64>;
//         type ResetOrigin = EnsureSignedBy<Four, u64>;
//         type WeightInfo = ();
//     }

//     type NodeAuthorization = Module<Test>;

//     fn new_test_ext() -> sp_io::TestExternalities {
//         let pub10: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//             hex!("0000000000000000000000000000000000000000000000000000000000000009")
//         ));
//         let pub20: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//             hex!("0000000000000000000000000000000000000000000000000000000000000013")
//         ));
//         let pub30: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//             hex!("000000000000000000000000000000000000000000000000000000000000001d")
//         ));
        
//         let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
//         GenesisConfig {
//             nodes: vec![pub10, pub20, pub30],
//         }.assimilate_storage(&mut t).unwrap();
//         t.into()
//     }

//     #[test]
//     fn add_node_works() {
//         new_test_ext().execute_with(|| {
//             let pub10: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("0000000000000000000000000000000000000000000000000000000000000009")
//             ));
//             let pub15: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("000000000000000000000000000000000000000000000000000000000000000e")
//             ));
//             let pub20: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("0000000000000000000000000000000000000000000000000000000000000013")
//             ));
//             let pub25: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("0000000000000000000000000000000000000000000000000000000000000018")
//             ));
//             let pub30: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("000000000000000000000000000000000000000000000000000000000000001d")
//             ));

//             assert_noop!(NodeAuthorization::add_well_known_node(Origin::signed(2), pub15.clone()), BadOrigin);
//             assert_noop!(
//                 NodeAuthorization::add_well_known_node(Origin::signed(1), pub20.clone()),
//                 Error::<Test>::AlreadyJoined
//             );
            
//             assert_ok!(NodeAuthorization::add_well_known_node(Origin::signed(1), pub15.clone()));
//             assert_eq!(
//                 NodeAuthorization::get_allow_list(),
//                 vec![pub10.clone(), pub15.clone(), pub20.clone(), pub30.clone()]
//             );
            
//             assert_noop!(
//                 NodeAuthorization::add_well_known_node(Origin::signed(1), pub25.clone()),
//                 Error::<Test>::TooManyNodes
//             );
//         });
//     }

//     #[test]
//     fn remove_node_works() {
//         new_test_ext().execute_with(|| {
//             let pub10: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("0000000000000000000000000000000000000000000000000000000000000009")
//             ));
//             let pub20: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("0000000000000000000000000000000000000000000000000000000000000013")
//             ));
//             let pub30: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("000000000000000000000000000000000000000000000000000000000000001d")
//             ));
//             let pub40: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("0000000000000000000000000000000000000000000000000000000000000027")
//             ));

//             assert_noop!(
//                 NodeAuthorization::remove_well_known_node(Origin::signed(3), pub20.clone()),
//                 BadOrigin
//             );
//             assert_noop!(
//                 NodeAuthorization::remove_well_known_node(Origin::signed(2), pub40.clone()),
//                 Error::<Test>::NotExist
//             );
            
//             assert_ok!(NodeAuthorization::remove_well_known_node(Origin::signed(2), pub20.clone()));
//             assert_eq!(NodeAuthorization::get_allow_list(), vec![pub10.clone(), pub30.clone()]);
//         });
//     }

//     #[test]
//     fn swap_node_works() {
//         new_test_ext().execute_with(|| {
//             let pub5: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("0000000000000000000000000000000000000000000000000000000000000004")
//             ));
//             let pub10: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("0000000000000000000000000000000000000000000000000000000000000009")
//             ));
//             let pub15: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("000000000000000000000000000000000000000000000000000000000000000e")
//             ));
//             let pub20: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("0000000000000000000000000000000000000000000000000000000000000013")
//             ));
//             let pub30: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("000000000000000000000000000000000000000000000000000000000000001d")
//             ));
            
//             assert_noop!(
//                 NodeAuthorization::swap_well_known_node(Origin::signed(4), pub20.clone(), pub5.clone()),
//                 BadOrigin
//             );
            
//             assert_ok!(NodeAuthorization::swap_well_known_node(Origin::signed(3), pub20.clone(), pub20.clone()));
//             assert_eq!(
//                 NodeAuthorization::get_allow_list(),
//                 vec![pub10.clone(), pub20.clone(), pub30.clone()]
//             );

//             assert_noop!(
//                 NodeAuthorization::swap_well_known_node(Origin::signed(3), pub15.clone(), pub5.clone()),
//                 Error::<Test>::NotExist
//             );
//             assert_noop!(
//                 NodeAuthorization::swap_well_known_node(Origin::signed(3), pub20.clone(), pub30.clone()),
//                 Error::<Test>::AlreadyJoined
//             );
            
//             assert_ok!(NodeAuthorization::swap_well_known_node(Origin::signed(3), pub20.clone(), pub5.clone()));
//             assert_eq!(
//                 NodeAuthorization::get_allow_list(),
//                 vec![pub5.clone(), pub10.clone(), pub30.clone()]
//             );
//         });
//     }

//     #[test]
//     fn reset_nodes_works() {
//         new_test_ext().execute_with(|| {
//             let pub5: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("0000000000000000000000000000000000000000000000000000000000000004")
//             ));
//             let pub15: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("000000000000000000000000000000000000000000000000000000000000000e")
//             ));
//             let pub20: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("0000000000000000000000000000000000000000000000000000000000000013")
//             ));
//             let pub25: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
//                 hex!("0000000000000000000000000000000000000000000000000000000000000018")
//             ));

//             assert_noop!(
//                 NodeAuthorization::reset_well_known_nodes(
//                     Origin::signed(3),
//                     vec![pub15.clone(), pub5.clone(), pub20.clone()]
//                 ),
//                 BadOrigin
//             );
//             assert_noop!(
//                 NodeAuthorization::reset_well_known_nodes(
//                     Origin::signed(4),
//                     vec![pub15.clone(), pub5.clone(), pub20.clone(), pub25.clone()]
//                 ),
//                 Error::<Test>::TooManyNodes
//             );
            
//             assert_ok!(
//                 NodeAuthorization::reset_well_known_nodes(
//                     Origin::signed(4),
//                     vec![pub15.clone(), pub5.clone(), pub20.clone()]
//                 )
//             );
//             assert_eq!(
//                 NodeAuthorization::get_allow_list(),
//                 vec![pub5.clone(), pub15.clone(), pub20.clone()]
//             );
//         });
//     }
// }