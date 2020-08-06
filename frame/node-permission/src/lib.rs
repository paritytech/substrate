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

use sp_core::{ed25519::Public, storage::well_known_keys};
use sp_std::prelude::*;
use frame_support::{
    decl_module, decl_storage, decl_event, decl_error,
    dispatch::DispatchResult, storage, ensure,
    traits::{Get, EnsureOrigin},
};

type NodeId = Public;

/// The module's config trait.
pub trait Trait: frame_system::Trait {
    /// The event type of this module.
	type Event: From<Event> + Into<<Self as frame_system::Trait>::Event>;

    /// The maximum number of permissioned nodes that are allowed to set
    type MaxPermissionedNodes: Get<u32>;

    /// The origin which can add a permissioned node.
    type AddNodeOrigin: EnsureOrigin<Self::Origin>;

    /// The origin which can reset the permissioned nodes.
    type ResetNodesOrigin: EnsureOrigin<Self::Origin>;
}

decl_storage! {
    trait Store for Module<T: Trait> as NodePermission {
    }
}

decl_event! {
    pub enum Event {
        /// The given node was added.
        NodeAdded,
    }
}

decl_error! {
    /// Error for the node permission module.
    pub enum Error for Module<T: Trait> {
        /// Too many permissioned nodes.
        TooManyNodes,
        AlreadyJoined,
    }
}

decl_module! {
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {
        /// The maximum number of permissioned nodes
        const MaxPermissionedNodes: u32 = T::MaxPermissionedNodes::get();

        type Error = Error<T>;

        fn deposit_event() = default;

        /// Add a node to the allowlist.
        ///
        /// Can only be called from `T::AddNodeOrigin`.
        #[weight = 0]
        pub fn add_node(origin, node_public_key: NodeId) -> DispatchResult {
            T::AddNodeOrigin::ensure_origin(origin)?;

            let mut nodes: Vec<NodeId> = storage::unhashed::get_or_default(well_known_keys::NODE_ALLOWLIST);
            ensure!(nodes.len() < T::MaxPermissionedNodes::get() as usize, Error::<T>::TooManyNodes);

            let location = nodes.binary_search(&node_public_key).err().ok_or(Error::<T>::AlreadyJoined)?;
            nodes.insert(location, node_public_key);
            storage::unhashed::put(well_known_keys::NODE_ALLOWLIST, &nodes);

            Self::deposit_event(Event::NodeAdded);

            Ok(())
        }
    }
}
