// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Substrate RPC implementation.
//!
//! A core implementation of Substrate RPC interfaces.

#![warn(missing_docs)]

use futures::{
	task::{FutureObj, Spawn, SpawnError},
	FutureExt,
};
use sp_core::traits::SpawnNamed;
use std::sync::Arc;

pub use rpc::IoHandlerExtension as RpcExtension;
pub use sc_rpc_api::{DenyUnsafe, Metadata};

pub mod author;
pub mod chain;
pub mod offchain;
pub mod state;
pub mod system;

#[cfg(any(test, feature = "test-helpers"))]
pub mod testing;

/// Task executor that is being used by RPC subscriptions.
#[derive(Clone)]
pub struct SubscriptionTaskExecutor(Arc<dyn SpawnNamed>);

impl SubscriptionTaskExecutor {
	/// Create a new `Self` with the given spawner.
	pub fn new(spawn: impl SpawnNamed + 'static) -> Self {
		Self(Arc::new(spawn))
	}
}

impl Spawn for SubscriptionTaskExecutor {
	fn spawn_obj(&self, future: FutureObj<'static, ()>) -> Result<(), SpawnError> {
		self.0.spawn("substrate-rpc-subscription", future.map(drop).boxed());
		Ok(())
	}

	fn status(&self) -> Result<(), SpawnError> {
		Ok(())
	}
}
