// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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
//!
//! The [`Client`] is one of the most important components of Substrate. It mainly comprises two
//! parts:
//!
//! - A database containing the blocks and chain state, generally referred to as
//! the [`Backend`](sc_client_api::backend::Backend).
//! - A runtime environment, generally referred to as the [`Executor`](CallExecutor).
//!
//! # Initialization
//!
//! Creating a [`Client`] is done by calling the `new` method and passing to it a
//! [`Backend`](sc_client_api::backend::Backend) and an [`Executor`](CallExecutor).
//!
//! The former is typically provided by the `sc-client-db` crate.
//!
//! The latter typically requires passing one of:
//!
//! - A [`LocalCallExecutor`] running the runtime locally.
//! - A [`RemoteCallExecutor`](light::call_executor::RemoteCallRequest) that will ask a
//! third-party to perform the executions.
//! - A [`RemoteOrLocalCallExecutor`](light::call_executor::RemoteOrLocalCallExecutor), combination
//! of the two.
//!
//! Additionally, the fourth generic parameter of the `Client` is a marker type representing
//! the ways in which the runtime can interface with the outside. Any code that builds a `Client`
//! is responsible for putting the right marker.
//!
//! ## Example
//!
//! ```
//! use std::sync::Arc;
//! use sc_client::{Client, in_mem::Backend, LocalCallExecutor};
//! use sp_runtime::Storage;
//! use sc_executor::{NativeExecutor, WasmExecutionMethod};
//!
//! // In this example, we're using the `Block` and `RuntimeApi` types from the
//! // `substrate-test-runtime-client` crate. These types are automatically generated when
//! // compiling a runtime. In a typical use-case, these types would have been to be generated
//! // from your runtime.
//! use substrate_test_runtime_client::{LocalExecutor, runtime::Block, runtime::RuntimeApi};
//!
//! let backend = Arc::new(Backend::<Block>::new());
//! let client = Client::<_, _, _, RuntimeApi>::new(
//! 	backend.clone(),
//! 	LocalCallExecutor::new(
//! 		backend.clone(),
//! 		NativeExecutor::<LocalExecutor>::new(WasmExecutionMethod::Interpreted, None),
//!		),
//! 	// This parameter provides the storage for the chain genesis.
//! 	&<Storage>::default(),
//! 	Default::default(),
//! 	Default::default(),
//! 	Default::default(),
//! );
//! ```
//!

#![warn(missing_docs)]
#![recursion_limit="128"]

pub mod cht;
pub mod in_mem;
pub mod genesis;
pub mod light;
pub mod leaves;
mod call_executor;
mod client;
mod block_rules;

pub use sc_client_api::{
	blockchain,
	blockchain::well_known_cache_keys,
	blockchain::Info as ChainInfo,
	notifications::{StorageEventStream, StorageChangeSet},
	call_executor::CallExecutor,
	utils,
};
pub use crate::{
	call_executor::LocalCallExecutor,
	client::{
		new_with_backend,
		new_in_mem,
		BlockBody, ImportNotifications, FinalityNotifications, BlockchainEvents, LockImportRun,
		BlockImportNotification, Client, ClientInfo, ExecutionStrategies, FinalityNotification,
		LongestChain, BlockOf, ProvideUncles, BadBlocks, ForkBlocks, apply_aux,
	},
	leaves::LeafSet,
};
pub use sp_state_machine::{ExecutionStrategy, StorageProof, StateMachine};
