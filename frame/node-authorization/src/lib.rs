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
//! This pallet manages a configurable set of nodes for a permissioned blockchain.
//! The node set is stored under [`well_known_keys::NODE_ALLOW_LIST`].

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use sp_core::{NodePublicKey, storage::well_known_keys};
use frame_support::{
    decl_module, decl_storage, decl_event, decl_error,
    storage, ensure,
    weights::{DispatchClass, Weight},
    traits::{Get, EnsureOrigin},
};
use codec::Encode;

pub trait WeightInfo {
    fn add_node() -> Weight;
    fn remove_node() -> Weight;
    fn swap_node() -> Weight;
    fn reset_nodes() -> Weight;
}

impl WeightInfo for () {
    fn add_node() -> Weight { 50_000_000 }
    fn remove_node() -> Weight { 50_000_000 }
    fn swap_node() -> Weight { 50_000_000 }
    fn reset_nodes() -> Weight { 50_000_000 }
}

pub trait Trait: frame_system::Trait {
    /// The event type of this module.
	type Event: From<Event> + Into<<Self as frame_system::Trait>::Event>;

    /// The maximum number of authorized nodes that are allowed to set
    type MaxAuthorizedNodes: Get<u32>;

    /// The origin which can add a authorized node.
    type AddOrigin: EnsureOrigin<Self::Origin>;

    /// The origin which can remove a authorized node.
    type RemoveOrigin: EnsureOrigin<Self::Origin>;

    /// The origin which can swap the authorized nodes.
    type SwapOrigin: EnsureOrigin<Self::Origin>;

    /// The origin which can reset the authorized nodes.
    type ResetOrigin: EnsureOrigin<Self::Origin>;

    /// Weight information for extrinsics in this pallet.
    type WeightInfo: WeightInfo;
}

decl_storage! {
    trait Store for Module<T: Trait> as NodeAuthorization {}
    add_extra_genesis {
        config(nodes): Vec<NodePublicKey>;
        build(|config: &GenesisConfig| {
            sp_io::storage::set(well_known_keys::NODE_ALLOW_LIST, &config.nodes.encode());
        });
    }
}

decl_event!(
    pub enum Event {
        /// The given node was added.
        NodeAdded(NodePublicKey),
        /// The given node was removed.
        NodeRemoved(NodePublicKey),
        /// Two given nodes were swapped; first item is removed, the latter is added.
        NodeSwapped(NodePublicKey, NodePublicKey),
        /// The given nodes were reset.
        NodesReset(Vec<NodePublicKey>),
    }
);

decl_error! {
    /// Error for the node authorization module.
    pub enum Error for Module<T: Trait> {
        /// Too many authorized nodes.
        TooManyNodes,
        /// The node is already joined in the list.
        AlreadyJoined,
        /// The node doesn't exist in the list.
        NotExist,
    }
}

decl_module! {
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {
        /// The maximum number of authorized nodes
        const MaxAuthorizedNodes: u32 = T::MaxAuthorizedNodes::get();

        type Error = Error<T>;

        fn deposit_event() = default;

        /// Add a node to the allow list.
        ///
        /// May only be called from `T::AddOrigin`.
        ///
        /// - `node_public_key`: identifier of the node, it's likely the public key of ed25519 keypair.
        #[weight = (T::WeightInfo::add_node(), DispatchClass::Operational)]
        pub fn add_node(origin, node_public_key: NodePublicKey) {
            T::AddOrigin::ensure_origin(origin)?;

            let mut nodes = Self::get_allow_list();
            ensure!(nodes.len() < T::MaxAuthorizedNodes::get() as usize, Error::<T>::TooManyNodes);

            let location = nodes.binary_search(&node_public_key).err().ok_or(Error::<T>::AlreadyJoined)?;
            nodes.insert(location, node_public_key.clone());
            Self::put_allow_list(&nodes);

            Self::deposit_event(Event::NodeAdded(node_public_key));
        }

        /// Remove a node from the allow list.
        ///
        /// May only be called from `T::RemoveOrigin`.
        ///
        /// - `node_public_key`: identifier of the node, it's likely the public key of ed25519 keypair.
        #[weight = (T::WeightInfo::remove_node(), DispatchClass::Operational)]
        pub fn remove_node(origin, node_public_key: NodePublicKey) {
            T::RemoveOrigin::ensure_origin(origin)?;

            let mut nodes = Self::get_allow_list();

            let location = nodes.binary_search(&node_public_key).ok().ok_or(Error::<T>::NotExist)?;
            nodes.remove(location);
            Self::put_allow_list(&nodes);

            Self::deposit_event(Event::NodeRemoved(node_public_key));
        }

        /// Swap two nodes.
        ///
        /// May only be called from `T::SwapOrigin`.
        ///
        /// - `remove`: the node which will be moved out from the list, it's likely the public key
        /// of ed25519 keypair.
        /// - `add`: the node which will be put in the list, it's likely the public key of ed25519
        /// keypair.
        #[weight = (T::WeightInfo::swap_node(), DispatchClass::Operational)]
        pub fn swap_node(origin, remove: NodePublicKey, add: NodePublicKey) {
            T::SwapOrigin::ensure_origin(origin)?;

            if remove == add { return Ok(()) }
            
            let mut nodes = Self::get_allow_list();
            let remove_location = nodes.binary_search(&remove).ok().ok_or(Error::<T>::NotExist)?;
            nodes.remove(remove_location);
            let add_location = nodes.binary_search(&add).err().ok_or(Error::<T>::AlreadyJoined)?;
            nodes.insert(add_location, add.clone());
            Self::put_allow_list(&nodes);

            Self::deposit_event(Event::NodeSwapped(remove, add));
        }
        
        /// Reset all the authorized nodes in the list.
        ///
        /// May only be called from `T::ResetOrigin`.
        ///
        /// - `nodes`: the new nodes for the allow list.
        #[weight = (T::WeightInfo::reset_nodes(), DispatchClass::Operational)]
        pub fn reset_nodes(origin, nodes: Vec<NodePublicKey>) {
            T::ResetOrigin::ensure_origin(origin)?;
            ensure!(nodes.len() < T::MaxAuthorizedNodes::get() as usize, Error::<T>::TooManyNodes);

            let mut nodes = nodes;
            nodes.sort();
            Self::put_allow_list(&nodes);

            Self::deposit_event(Event::NodesReset(nodes));
        }
    }
}

impl<T: Trait> Module<T> {
    fn get_allow_list() -> Vec<NodePublicKey> {
        storage::unhashed::get_or_default(well_known_keys::NODE_ALLOW_LIST)
    }

    fn put_allow_list(nodes: &Vec<NodePublicKey>) {
        storage::unhashed::put(well_known_keys::NODE_ALLOW_LIST, nodes);
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
    use hex_literal::hex;

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
        pub const MaxAuthorizedNodes: u32 = 4;
    }
    impl Trait for Test {
        type Event = ();
        type MaxAuthorizedNodes = MaxAuthorizedNodes;
        type AddOrigin = EnsureSignedBy<One, u64>;
        type RemoveOrigin = EnsureSignedBy<Two, u64>;
        type SwapOrigin = EnsureSignedBy<Three, u64>;
        type ResetOrigin = EnsureSignedBy<Four, u64>;
        type WeightInfo = ();
    }

    type NodeAuthorization = Module<Test>;

    fn new_test_ext() -> sp_io::TestExternalities {
        let pub10: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
            hex!("0000000000000000000000000000000000000000000000000000000000000009")
        ));
        let pub20: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
            hex!("0000000000000000000000000000000000000000000000000000000000000013")
        ));
        let pub30: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
            hex!("000000000000000000000000000000000000000000000000000000000000001d")
        ));
        
        let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
        GenesisConfig {
            nodes: vec![pub10, pub20, pub30],
        }.assimilate_storage(&mut t).unwrap();
        t.into()
    }

    #[test]
    fn add_node_works() {
        new_test_ext().execute_with(|| {
            let pub10: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("0000000000000000000000000000000000000000000000000000000000000009")
            ));
            let pub15: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("000000000000000000000000000000000000000000000000000000000000000e")
            ));
            let pub20: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("0000000000000000000000000000000000000000000000000000000000000013")
            ));
            let pub25: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("0000000000000000000000000000000000000000000000000000000000000018")
            ));
            let pub30: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("000000000000000000000000000000000000000000000000000000000000001d")
            ));

            assert_noop!(NodeAuthorization::add_node(Origin::signed(2), pub15.clone()), BadOrigin);
            assert_noop!(
                NodeAuthorization::add_node(Origin::signed(1), pub20.clone()),
                Error::<Test>::AlreadyJoined
            );
            
            assert_ok!(NodeAuthorization::add_node(Origin::signed(1), pub15.clone()));
            assert_eq!(
                NodeAuthorization::get_allow_list(),
                vec![pub10.clone(), pub15.clone(), pub20.clone(), pub30.clone()]
            );
            
            assert_noop!(
                NodeAuthorization::add_node(Origin::signed(1), pub25.clone()),
                Error::<Test>::TooManyNodes
            );
        });
    }

    #[test]
    fn remove_node_works() {
        new_test_ext().execute_with(|| {
            let pub10: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("0000000000000000000000000000000000000000000000000000000000000009")
            ));
            let pub20: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("0000000000000000000000000000000000000000000000000000000000000013")
            ));
            let pub30: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("000000000000000000000000000000000000000000000000000000000000001d")
            ));
            let pub40: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("0000000000000000000000000000000000000000000000000000000000000027")
            ));

            assert_noop!(
                NodeAuthorization::remove_node(Origin::signed(3), pub20.clone()),
                BadOrigin
            );
            assert_noop!(
                NodeAuthorization::remove_node(Origin::signed(2), pub40.clone()),
                Error::<Test>::NotExist
            );
            
            assert_ok!(NodeAuthorization::remove_node(Origin::signed(2), pub20.clone()));
            assert_eq!(NodeAuthorization::get_allow_list(), vec![pub10.clone(), pub30.clone()]);
        });
    }

    #[test]
    fn swap_node_works() {
        new_test_ext().execute_with(|| {
            let pub5: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("0000000000000000000000000000000000000000000000000000000000000004")
            ));
            let pub10: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("0000000000000000000000000000000000000000000000000000000000000009")
            ));
            let pub15: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("000000000000000000000000000000000000000000000000000000000000000e")
            ));
            let pub20: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("0000000000000000000000000000000000000000000000000000000000000013")
            ));
            let pub30: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("000000000000000000000000000000000000000000000000000000000000001d")
            ));
            
            assert_noop!(
                NodeAuthorization::swap_node(Origin::signed(4), pub20.clone(), pub5.clone()),
                BadOrigin
            );
            
            assert_ok!(NodeAuthorization::swap_node(Origin::signed(3), pub20.clone(), pub20.clone()));
            assert_eq!(
                NodeAuthorization::get_allow_list(),
                vec![pub10.clone(), pub20.clone(), pub30.clone()]
            );

            assert_noop!(
                NodeAuthorization::swap_node(Origin::signed(3), pub15.clone(), pub5.clone()),
                Error::<Test>::NotExist
            );
            assert_noop!(
                NodeAuthorization::swap_node(Origin::signed(3), pub20.clone(), pub30.clone()),
                Error::<Test>::AlreadyJoined
            );
            
            assert_ok!(NodeAuthorization::swap_node(Origin::signed(3), pub20.clone(), pub5.clone()));
            assert_eq!(
                NodeAuthorization::get_allow_list(),
                vec![pub5.clone(), pub10.clone(), pub30.clone()]
            );
        });
    }

    #[test]
    fn reset_nodes_works() {
        new_test_ext().execute_with(|| {
            let pub5: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("0000000000000000000000000000000000000000000000000000000000000004")
            ));
            let pub15: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("000000000000000000000000000000000000000000000000000000000000000e")
            ));
            let pub20: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("0000000000000000000000000000000000000000000000000000000000000013")
            ));
            let pub25: NodePublicKey = NodePublicKey::Ed25519(Public::from_raw(
                hex!("0000000000000000000000000000000000000000000000000000000000000018")
            ));

            assert_noop!(
                NodeAuthorization::reset_nodes(
                    Origin::signed(3),
                    vec![pub15.clone(), pub5.clone(), pub20.clone()]
                ),
                BadOrigin
            );
            assert_noop!(
                NodeAuthorization::reset_nodes(
                    Origin::signed(4),
                    vec![pub15.clone(), pub5.clone(), pub20.clone(), pub25.clone()]
                ),
                Error::<Test>::TooManyNodes
            );
            
            assert_ok!(
                NodeAuthorization::reset_nodes(
                    Origin::signed(4),
                    vec![pub15.clone(), pub5.clone(), pub20.clone()]
                )
            );
            assert_eq!(
                NodeAuthorization::get_allow_list(),
                vec![pub5.clone(), pub15.clone(), pub20.clone()]
            );
        });
    }
}
