// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

#![warn(missing_docs)]

//! Node-specific RPC methods for interaction with Balances pallet.

use std::{sync::Arc};


/// Balances RPC methods.
#[rpc]
pub trait BalancesApi<T> {

    #[rpc(name="balances_freeBalance")]
    fn free_balance(&self, who: impl sp_std::borrow::Borrow<T::AccountId>) -> Result<T::Balance>;
}

/// A struct that implements the ['BalancesApi'].
pub struct Balances<C> {
    client: Arc<C>,
}

impl<C> Balances<C> {
    /// Create new `Balances` with the given reference to the client.
	pub fn new(client: Arc<C>) -> Self {
		Self { client, _marker: Default::default() }
	}
}

impl<T> BalancesApi for Balances {
    fn free_balance(&self, who: impl sp_std::borrow::Borrow<T::AccountId>) -> Result<T::Balance> {
        //call client
    }
}