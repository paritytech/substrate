// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Substrate RPC interfaces.
//!
//! A collection of RPC methods and subscriptions supported by all substrate clients.

#![warn(missing_docs)]

mod errors;
mod helpers;
mod metadata;
mod policy;

pub use helpers::Receiver;
pub use jsonrpc_core::IoHandlerExtension as RpcExtension;
pub use metadata::Metadata;
pub use policy::{DenyUnsafe, UnsafeRpcError};

pub mod author;
pub mod chain;
pub mod child_state;
pub mod offchain;
pub mod state;
pub mod system;
