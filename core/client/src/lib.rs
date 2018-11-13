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

//! Substrate Client and associated logic.

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]
#![recursion_limit="128"]

#[cfg(feature = "std")]
extern crate substrate_trie as trie;
extern crate parity_codec as codec;
extern crate substrate_primitives as primitives;
extern crate sr_primitives as runtime_primitives;
#[cfg(feature = "std")]
extern crate substrate_state_machine as state_machine;
#[cfg(feature = "std")]
extern crate substrate_consensus_common as consensus;
extern crate sr_version as runtime_version;
extern crate sr_std as rstd;
#[cfg(test)]
extern crate substrate_keyring as keyring;
#[cfg(test)]
extern crate substrate_test_client as test_client;
#[cfg(feature = "std")]
#[macro_use]
extern crate substrate_telemetry;
#[cfg(feature = "std")]
#[macro_use]
extern crate slog;	// needed until we can reexport `slog_info` from `substrate_telemetry`

#[cfg(feature = "std")]
extern crate fnv;
#[cfg(feature = "std")]
extern crate futures;
#[cfg(feature = "std")]
extern crate parking_lot;
#[cfg(feature = "std")]
extern crate hash_db;
#[cfg(feature = "std")]
extern crate heapsize;
#[cfg(feature = "std")]
extern crate kvdb;

#[cfg(feature = "std")]
#[macro_use]
extern crate error_chain;
#[cfg(feature = "std")]
#[macro_use]
extern crate log;
#[cfg(feature = "std")]
#[cfg_attr(test, macro_use)]
extern crate substrate_executor as executor;
#[cfg(test)]
#[macro_use]
extern crate hex_literal;
#[cfg(feature = "std")]
#[cfg(test)]
extern crate kvdb_memorydb;

#[macro_use]
pub mod runtime_api;
#[cfg(feature = "std")]
pub mod error;
#[cfg(feature = "std")]
pub mod blockchain;
#[cfg(feature = "std")]
pub mod backend;
#[cfg(feature = "std")]
pub mod cht;
#[cfg(feature = "std")]
pub mod in_mem;
#[cfg(feature = "std")]
pub mod genesis;
pub mod block_builder;
#[cfg(feature = "std")]
pub mod light;
#[cfg(feature = "std")]
mod leaves;
#[cfg(feature = "std")]
mod call_executor;
#[cfg(feature = "std")]
mod client;
#[cfg(feature = "std")]
mod notifications;

#[cfg(feature = "std")]
pub use blockchain::Info as ChainInfo;
#[cfg(feature = "std")]
pub use call_executor::{CallResult, CallExecutor, LocalCallExecutor};
#[cfg(feature = "std")]
pub use client::{
	new_with_backend,
	new_in_mem,
	BlockBody, BlockStatus, ImportNotifications, FinalityNotifications, BlockchainEvents,
	Client, ClientInfo, ChainHead,
};
#[cfg(feature = "std")]
pub use notifications::{StorageEventStream, StorageChangeSet};
#[cfg(feature = "std")]
pub use state_machine::ExecutionStrategy;
#[cfg(feature = "std")]
pub use leaves::LeafSet;
