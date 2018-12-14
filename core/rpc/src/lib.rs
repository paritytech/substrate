// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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
extern crate parity_codec as codec;
extern crate parking_lot;
extern crate serde_json;
extern crate sr_primitives as runtime_primitives;
extern crate sr_version as runtime_version;
extern crate substrate_client as client;
extern crate substrate_network as network;
extern crate substrate_primitives as primitives;
extern crate substrate_transaction_pool as transaction_pool;
extern crate tokio;

#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate jsonrpc_macros;
#[macro_use]
extern crate log;
#[macro_use]
extern crate serde_derive;

#[cfg(test)]
#[macro_use]
extern crate assert_matches;
#[cfg(test)]
#[macro_use]
extern crate hex_literal;
#[cfg(test)]
extern crate substrate_test_client as test_client;
#[cfg(test)]
extern crate substrate_consensus_common as consensus;
#[cfg(test)]
extern crate rustc_hex;

mod errors;
mod helpers;
mod subscriptions;

pub use subscriptions::Subscriptions;

pub mod author;
pub mod chain;
pub mod metadata;
pub mod state;
pub mod system;
