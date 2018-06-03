// Copyright 2017 Parity Technologies (UK) Ltd.
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

#![warn(missing_docs)]

extern crate jsonrpc_core as rpc;
extern crate jsonrpc_pubsub;
extern crate parking_lot;
extern crate substrate_client as client;
extern crate substrate_extrinsic_pool as extrinsic_pool;
extern crate substrate_primitives as primitives;
extern crate substrate_state_machine as state_machine;
extern crate tokio_core;

#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate jsonrpc_macros;
#[macro_use]
extern crate log;

#[cfg(test)]
#[macro_use]
extern crate assert_matches;
#[cfg(test)]
extern crate substrate_test_client as test_client;

mod subscriptions;

pub mod author;
pub mod chain;
pub mod metadata;
pub mod state;
pub mod system;
