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

//! Substrate Client and associated logic.

#![warn(missing_docs)]
#![recursion_limit="128"]

extern crate substrate_bft as bft;
extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_state_machine as state_machine;
#[cfg(test)] extern crate substrate_keyring as keyring;
#[cfg(test)] extern crate substrate_test_client as test_client;

extern crate ed25519;
extern crate futures;
extern crate parking_lot;
extern crate triehash;

#[macro_use] extern crate error_chain;
#[macro_use] extern crate log;
#[cfg(test)] #[macro_use] extern crate substrate_executor as executor;
#[cfg(test)] #[macro_use] extern crate hex_literal;

pub mod error;
pub mod blockchain;
pub mod backend;
pub mod in_mem;
pub mod genesis;
pub mod block_builder;
pub mod light;
mod call_executor;
mod client;

pub use client::{
	new_in_mem,
	BlockStatus, BlockOrigin, BlockchainEventStream, BlockchainEvents,
	Client, ClientInfo, ChainHead,
	ImportResult, GenesisBuilder,
};
pub use blockchain::Info as ChainInfo;
pub use call_executor::{
	CallResult, CallExecutor, LocalCallExecutor, RemoteCallExecutor,
};
