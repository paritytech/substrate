// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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
use jsonrpc_derive::rpc;
use jsonrpc_core::{Error, ErrorCode};
use futures::channel::{oneshot, mpsc};
use futures::{SinkExt, FutureExt, TryFutureExt};

/// FutureResult
type FutureResult<T> = Box<dyn jsonrpc_core::futures::Future<Item = T, Error = Error> + Send>;

/// RPC interface for upgrading runtimes.
#[rpc]
pub trait RuntimeUpgradeApi {
    /// Instructs the test-runner to upgrade the runtime with the given wasm.
    #[rpc(name = "engine_upgradeRuntime")]
    fn upgrade_runtime(&self, wasm: Vec<u8> ) -> FutureResult<()>;
}

/// Implements the [`RuntimeUpgradeApi`]
pub struct RuntimeUpgrade {
    wasm_channel: mpsc::Sender<UpgradeRequest>,
}

impl RuntimeUpgrade {
    /// Constructor
    pub fn new(wasm_channel: mpsc::Sender<UpgradeRequest>) -> Self {
        Self { wasm_channel }
    }
}

/// A message to the upgrade runtime task.
pub struct UpgradeRequest {
    /// wasm blob
    pub wasm: Vec<u8>,
    /// sender to respond with errors
    pub sender: oneshot::Sender<()>
}

impl RuntimeUpgradeApi for RuntimeUpgrade {
    fn upgrade_runtime(&self, wasm: Vec<u8> ) -> FutureResult<()> {
        let mut sink = self.wasm_channel.clone();
        let future = async move {
            let (sender, receiver) = oneshot::channel();
            let request = UpgradeRequest {
                wasm,
                sender,
            };
            sink.send(request).await
                .map_err(|_| format!("upgrade request task is dropped."))?;
            receiver.await
                .map_err(|_| format!("upgrade request task is dropped."))?;
            Ok(())
        }.boxed();

        Box::new(
            future
                .map_err(|message| {
                    Error {
                        message,
                        code: ErrorCode::InternalError,
                        data: None
                    }
                })
                .compat()
        )
    }
}