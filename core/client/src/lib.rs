// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
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
	BlockImportNotification, Client, ClientInfo, ChainHead, ExecutionStrategies,
};
#[cfg(feature = "std")]
pub use crate::notifications::{StorageEventStream, StorageChangeSet};
#[cfg(feature = "std")]
pub use state_machine::ExecutionStrategy;
#[cfg(feature = "std")]
pub use crate::leaves::LeafSet;

#[doc(inline)]
pub use sr_api_macros::{decl_runtime_apis, impl_runtime_apis};
