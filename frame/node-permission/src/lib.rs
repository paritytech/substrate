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

//! # Node permission moudule
//!
//! This module is used by the `client/peerset` to retrieve the current
//! permissioned nodes.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use sp_std::fmt::Debug;
use sp_core::storage::well_known_keys;
use sp_runtime::traits::{Member, MaybeSerializeDeserialize, MaybeDisplay};
use frame_support::{
    decl_module, decl_storage, decl_event, decl_error,
    Parameter, storage, ensure, traits::{Get, EnsureOrigin},
};
use codec::Encode;

pub trait Trait: frame_system::Trait {
    /// The event type of this module.
	type Event: From<Event> + Into<<Self as frame_system::Trait>::Event>;

    /// The maximum number of permissioned nodes that are allowed to set
    type MaxPermissionedNodes: Get<u32>;

    /// The node identifier type for the runtime.
    type NodeId: Parameter + Member + MaybeSerializeDeserialize + Debug + MaybeDisplay
        + Ord + Default;

    /// The origin which can add a permissioned node.
    type AddOrigin: EnsureOrigin<Self::Origin>;

    /// The origin which can remove a permissioned node.
    type RemoveOrigin: EnsureOrigin<Self::Origin>;

    /// The origin which can swap the permissioned nodes.
    type SwapOrigin: EnsureOrigin<Self::Origin>;

    /// The origin which can reset the permissioned nodes.
    type ResetOrigin: EnsureOrigin<Self::Origin>;
}

decl_storage! {
    trait Store for Module<T: Trait> as NodePermission {}
    add_extra_genesis {
        config(nodes): Vec<T::NodeId>;
        build(|config: &GenesisConfig<T>| {
            sp_io::storage::set(well_known_keys::NODE_ALLOWLIST, &config.nodes.encode());
        });
    }
}

decl_event! {
    pub enum Event {
        /// The given node was added; see the transaction for node id.
        NodeAdded,
        /// The given node was removed; see the transaction for node id.
        NodeRemoved,
        /// Two given nodes were swapped; see the transaction for node id.
        NodesSwapped,
        /// The given nodes were reset; see the transaction for new set.
        NodesReset,
    }
}

decl_error! {
    /// Error for the node permission module.
    pub enum Error for Module<T: Trait> {
        /// Too many permissioned nodes.
        TooManyNodes,
        /// The node is already joined in the list.
        AlreadyJoined,
        /// The node doesn't exist in the list.
        NotExist,
    }
}

decl_module! {
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {
        /// The maximum number of permissioned nodes
        const MaxPermissionedNodes: u32 = T::MaxPermissionedNodes::get();

        type Error = Error<T>;

        fn deposit_event() = default;

        /// Add a node id to the allowlist. It's likely the public key of ed25519 keypair.
        ///
        /// May only be called from `T::AddOrigin`.
        #[weight = 0]
        pub fn add_node(origin, node_id: T::NodeId) {
            T::AddOrigin::ensure_origin(origin)?;

            let mut nodes = Self::get_allowlist();
            ensure!(nodes.len() < T::MaxPermissionedNodes::get() as usize, Error::<T>::TooManyNodes);

            let location = nodes.binary_search(&node_id).err().ok_or(Error::<T>::AlreadyJoined)?;
            nodes.insert(location, node_id);
            Self::put_allowlist(nodes);

            Self::deposit_event(Event::NodeAdded);
        }

        /// Remove a node from te allowlist. It's likely the public key of ed25519 keypair.
        ///
        /// May only be called from `T::RemoveOrigin`.
        #[weight = 0]
        pub fn remove_node(origin, node_id: T::NodeId) {
            T::RemoveOrigin::ensure_origin(origin)?;

            let mut nodes = Self::get_allowlist();

            let location = nodes.binary_search(&node_id).ok().ok_or(Error::<T>::NotExist)?;
            nodes.remove(location);
            Self::put_allowlist(nodes);

            Self::deposit_event(Event::NodeRemoved);
        }

        /// Swap two nodes; `remove` is the one which will be put out of the list,
        /// `add` will be in the list.
        ///
        /// May only be called from `T::SwapOrigin`.
        #[weight = 0]
        pub fn swap_node(origin, remove: T::NodeId, add: T::NodeId) {
            T::SwapOrigin::ensure_origin(origin)?;

            if remove == add { return Ok(()) }
            
            let mut nodes = Self::get_allowlist();
            let location = nodes.binary_search(&remove).ok().ok_or(Error::<T>::NotExist)?;
            let _ = nodes.binary_search(&add).err().ok_or(Error::<T>::AlreadyJoined)?;
            nodes[location] = add;
            nodes.sort();
            Self::put_allowlist(nodes);

            Self::deposit_event(Event::NodesSwapped);
        }

        /// Reset all the permissioned nodes in the list.
        ///
        /// May only be called from `T::ResetOrigin`.
        #[weight = 0]
        pub fn reset_nodes(origin, nodes: Vec<T::NodeId>) {
            T::ResetOrigin::ensure_origin(origin)?;
            ensure!(nodes.len() < T::MaxPermissionedNodes::get() as usize, Error::<T>::TooManyNodes);

            let mut nodes = nodes;
            nodes.sort();
            Self::put_allowlist(nodes);

            Self::deposit_event(Event::NodesReset);
        }
    }
}

impl<T: Trait> Module<T> {
    fn get_allowlist() -> Vec<T::NodeId> {
        storage::unhashed::get_or_default(well_known_keys::NODE_ALLOWLIST)
    }

    fn put_allowlist(nodes: Vec<T::NodeId>) {
        storage::unhashed::put(well_known_keys::NODE_ALLOWLIST, &nodes);
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
    use sp_core::H256;
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
        pub const MaxPermissionedNodes: u32 = 4;
    }
    impl Trait for Test {
        type Event = ();
        type MaxPermissionedNodes = MaxPermissionedNodes;
        type NodeId = u64;
        type AddOrigin = EnsureSignedBy<One, u64>;
        type RemoveOrigin = EnsureSignedBy<Two, u64>;
        type SwapOrigin = EnsureSignedBy<Three, u64>;
        type ResetOrigin = EnsureSignedBy<Four, u64>;
    }

    type NodePermission = Module<Test>;

    fn new_test_ext() -> sp_io::TestExternalities {
        let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
        GenesisConfig::<Test>{
            nodes: vec![10, 20, 30],
        }.assimilate_storage(&mut t).unwrap();
        t.into()
    }

    #[test]
    fn add_node_works() {
        new_test_ext().execute_with(|| {
            assert_noop!(NodePermission::add_node(Origin::signed(2), 15), BadOrigin);
            assert_noop!(NodePermission::add_node(Origin::signed(1), 20), Error::<Test>::AlreadyJoined);
            
            assert_ok!(NodePermission::add_node(Origin::signed(1), 15));
            assert_eq!(NodePermission::get_allowlist(), vec![10, 15, 20, 30]);
            
            assert_noop!(NodePermission::add_node(Origin::signed(1), 25), Error::<Test>::TooManyNodes);
        });
    }

    #[test]
    fn remove_node_works() {
        new_test_ext().execute_with(|| {
            assert_noop!(NodePermission::remove_node(Origin::signed(3), 20), BadOrigin);
            assert_noop!(NodePermission::remove_node(Origin::signed(2), 40), Error::<Test>::NotExist);
            
            assert_ok!(NodePermission::remove_node(Origin::signed(2), 20));
            assert_eq!(NodePermission::get_allowlist(), vec![10, 30]);
        });
    }

    #[test]
    fn swap_node_works() {
        new_test_ext().execute_with(|| {
            assert_noop!(NodePermission::swap_node(Origin::signed(4), 20, 5), BadOrigin);
            
            assert_ok!(NodePermission::swap_node(Origin::signed(3), 20, 20));
            assert_eq!(NodePermission::get_allowlist(), vec![10, 20, 30]);

            assert_noop!(NodePermission::swap_node(Origin::signed(3), 15, 5), Error::<Test>::NotExist);
            assert_noop!(NodePermission::swap_node(Origin::signed(3), 20, 30), Error::<Test>::AlreadyJoined);
            
            assert_ok!(NodePermission::swap_node(Origin::signed(3), 20, 5));
            assert_eq!(NodePermission::get_allowlist(), vec![5, 10, 30]);
        });
    }

    #[test]
    fn reset_nodes_works() {
        new_test_ext().execute_with(|| {
            assert_noop!(NodePermission::reset_nodes(Origin::signed(3), vec![15, 5, 20]), BadOrigin);
            assert_noop!(NodePermission::reset_nodes(Origin::signed(4), vec![15, 5, 20, 25]), Error::<Test>::TooManyNodes);
            
            assert_ok!(NodePermission::reset_nodes(Origin::signed(4), vec![15, 5, 20]));
            assert_eq!(NodePermission::get_allowlist(), vec![5, 15, 20]);
        });
    }
}
