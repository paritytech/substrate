// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
pub mod leaves;
#[cfg(feature = "std")]
pub mod children;
#[cfg(feature = "std")]
mod call_executor;
#[cfg(feature = "std")]
mod client;
#[cfg(feature = "std")]
mod notifications;


#[cfg(feature = "std")]
pub use crate::blockchain::Info as ChainInfo;
#[cfg(feature = "std")]
pub use crate::call_executor::{CallExecutor, LocalCallExecutor};
#[cfg(feature = "std")]
pub use crate::client::{
	new_with_backend,
	new_in_mem,
	BlockBody, BlockStatus, ImportNotifications, FinalityNotifications, BlockchainEvents,
	BlockImportNotification, Client, ClientInfo, ExecutionStrategies,
	LongestChain
};
#[cfg(feature = "std")]
pub use crate::notifications::{StorageEventStream, StorageChangeSet};
#[cfg(feature = "std")]
pub use state_machine::ExecutionStrategy;
#[cfg(feature = "std")]
pub use crate::leaves::LeafSet;

#[doc(inline)]
pub use sr_api_macros::{decl_runtime_apis, impl_runtime_apis};
