// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

#![cfg(unix)]

use tokio;
use node_primitives::{Hash,AccountIndex};

use sc_rpc::state::{
	StateClient,
};
use substrate_frame_rpc_system::SystemClient;
use substrate_frame_rpc_support::StorageQuery;
use sp_keyring::AccountKeyring;
use futures::compat::Future01CompatExt;
pub mod common;

#[tokio::test(core_threads = 2)]
async fn test_transfer() -> Result<(), Box<dyn std::error::Error>> {
    let client = common::BlackBoxClient::default().await?;
    let rpc : SystemClient<Hash, AccountIndex> = client.rpc();
    println!("got ma client");
    let prev_nonce = rpc.nonce(AccountKeyring::Alice.into())
        .compat()
        .await
        .expect("RPC is connected");
    assert_eq!(prev_nonce, 100, "Nonce is different");
    // let q = StorageQuery::value::<LastActionId>();
    // let _: Option<u64> = q.get(&cl, None).await?;
    Ok(())
}