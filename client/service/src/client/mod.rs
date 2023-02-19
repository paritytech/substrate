// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Substrate Client and associated logic.
//!
//! The [`Client`] is one of the most important components of Substrate. It mainly comprises two
//! parts:
//!
//! - A database containing the blocks and chain state, generally referred to as
//! the [`Backend`](sc_client_api::backend::Backend).
//! - A runtime environment, generally referred to as the
//! [`Executor`](sc_client_api::call_executor::CallExecutor).
//!
//! # Initialization
//!
//! Creating a [`Client`] is done by calling the `new` method and passing to it a
//! [`Backend`](sc_client_api::backend::Backend) and an
//! [`Executor`](sc_client_api::call_executor::CallExecutor).
//!
//! The former is typically provided by the `sc-client-db` crate.
//!
//! The latter typically requires passing one of:
//!
//! - A [`LocalCallExecutor`] running the runtime locally.
//! - A `RemoteCallExecutor` that will ask a third-party to perform the executions.
//! - A `RemoteOrLocalCallExecutor` combination of the two.
//!
//! Additionally, the fourth generic parameter of the `Client` is a marker type representing
//! the ways in which the runtime can interface with the outside. Any code that builds a `Client`
//! is responsible for putting the right marker.

mod block_rules;
mod call_executor;
mod client;
pub mod genesis;
mod wasm_override;
mod wasm_substitutes;

pub use self::{
	call_executor::LocalCallExecutor,
	client::{resolve_state_version_from_wasm, Client, ClientConfig},
};

#[cfg(feature = "test-helpers")]
pub use self::client::{new_in_mem, new_with_backend};
