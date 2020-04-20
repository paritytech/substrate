// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Substrate RPC interfaces.
//!
//! A collection of RPC methods and subscriptions supported by all substrate clients.

#![warn(missing_docs)]

mod errors;
mod helpers;
mod policy;
mod subscriptions;

pub use jsonrpc_core::IoHandlerExtension as RpcExtension;
pub use subscriptions::{Subscriptions, TaskExecutor};
pub use helpers::Receiver;
pub use policy::DenyUnsafe;

pub mod author;
pub mod chain;
pub mod offchain;
pub mod state;
pub mod child_state;
pub mod system;
