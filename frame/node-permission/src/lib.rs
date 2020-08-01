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

use frame_support::{decl_module, decl_storage, dispatch::DispatchResult};
use frame_system::ensure_signed;
use sp_node_permission::NodeId;

/// The module's config trait.
pub trait Trait: frame_system::Trait {}

decl_storage! {
    trait Store for Module<T: Trait> as NodePermission {
        /// Public keys of the permissioned nodes.
        // TODO add genesis config
        NodePublicKeys get(fn node_public_keys): Vec<NodeId>;
    }
}

decl_module! {
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {
        // type Error = Error<T>;

        // fn deposit_event() = default;

        /// Add a node to the allowlist.
        #[weight = 0]
        pub fn add_node(origin, node_public_key: NodeId) -> DispatchResult {
            // TODO ensure to be coucil/root
            let _who = ensure_signed(origin)?;

            NodePublicKeys::mutate(|old| old.push(node_public_key));

            Ok(())
        }
    }
}
