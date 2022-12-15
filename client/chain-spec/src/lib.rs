// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Substrate chain configurations.
//!
//! This crate contains structs and utilities to declare
//! a runtime-specific configuration file (a.k.a chain spec).
//!
//! Basic chain spec type containing all required parameters is
//! [`GenericChainSpec`]. It can be extended with
//! additional options that contain configuration specific to your chain.
//! Usually the extension is going to be an amalgamate of types exposed
//! by Substrate core modules. To allow the core modules to retrieve
//! their configuration from your extension you should use `ChainSpecExtension`
//! macro exposed by this crate.
//!
//! ```rust
//! use std::collections::HashMap;
//! use sc_chain_spec::{GenericChainSpec, ChainSpecExtension};
//!
//! #[derive(Clone, Debug, serde::Serialize, serde::Deserialize, ChainSpecExtension)]
//! pub struct MyExtension {
//! 		pub known_blocks: HashMap<u64, String>,
//! }
//!
//! pub type MyChainSpec<G> = GenericChainSpec<G, MyExtension>;
//! ```
//!
//! Some parameters may require different values depending on the
//! current blockchain height (a.k.a. forks). You can use `ChainSpecGroup`
//! macro and provided [`Forks`](./struct.Forks.html) structure to put
//! such parameters to your chain spec.
//! This will allow to override a single parameter starting at specific
//! block number.
//!
//! ```rust
//! use sc_chain_spec::{Forks, ChainSpecGroup, ChainSpecExtension, GenericChainSpec};
//!
//! #[derive(Clone, Debug, serde::Serialize, serde::Deserialize, ChainSpecGroup)]
//! pub struct ClientParams {
//! 	max_block_size: usize,
//! 	max_extrinsic_size: usize,
//! }
//!
//! #[derive(Clone, Debug, serde::Serialize, serde::Deserialize, ChainSpecGroup)]
//! pub struct PoolParams {
//! 	max_transaction_size: usize,
//! }
//!
//! #[derive(Clone, Debug, serde::Serialize, serde::Deserialize, ChainSpecGroup, ChainSpecExtension)]
//! pub struct Extension {
//! 	pub client: ClientParams,
//! 	pub pool: PoolParams,
//! }
//!
//! pub type BlockNumber = u64;
//!
//! /// A chain spec supporting forkable `ClientParams`.
//! pub type MyChainSpec1<G> = GenericChainSpec<G, Forks<BlockNumber, ClientParams>>;
//!
//! /// A chain spec supporting forkable `Extension`.
//! pub type MyChainSpec2<G> = GenericChainSpec<G, Forks<BlockNumber, Extension>>;
//! ```
//!
//! It's also possible to have a set of parameters that is allowed to change
//! with block numbers (i.e. is forkable), and another set that is not subject to changes.
//! This is also possible by declaring an extension that contains `Forks` within it.
//!
//!
//! ```rust
//! use serde::{Serialize, Deserialize};
//! use sc_chain_spec::{Forks, GenericChainSpec, ChainSpecGroup, ChainSpecExtension};
//!
//! #[derive(Clone, Debug, Serialize, Deserialize, ChainSpecGroup)]
//! pub struct ClientParams {
//! 	max_block_size: usize,
//! 	max_extrinsic_size: usize,
//! }
//!
//! #[derive(Clone, Debug, Serialize, Deserialize, ChainSpecGroup)]
//! pub struct PoolParams {
//! 	max_transaction_size: usize,
//! }
//!
//! #[derive(Clone, Debug, Serialize, Deserialize, ChainSpecExtension)]
//! pub struct Extension {
//! 	pub client: ClientParams,
//! 	#[forks]
//! 	pub pool: Forks<u64, PoolParams>,
//! }
//!
//! pub type MyChainSpec<G> = GenericChainSpec<G, Extension>;
//! ```
//!
//! # Substrate chain specification format
//!
//! The Substrate chain specification is a `json` file that describes the basics of a chain. Most
//! importantly it lays out the genesis storage which leads to the genesis hash. The default
//! Substrate chain specification format is the following:
//!
//! ```json
//! // The human readable name of the chain.
//! "name": "Flaming Fir",
//! // The id of the chain.
//! "id": "flamingfir9",
//! // The chain type of this chain.
//! // Possible values are `Live`, `Development`, `Local`.
//! "chainType": "Live",
//! // A list of multi addresses that belong to boot nodes of the chain.
//! "bootNodes": [
//!   "/dns/0.flamingfir.paritytech.net/tcp/30333/p2p/12D3KooWLK2gMLhWsYJzjW3q35zAs9FDDVqfqVfVuskiGZGRSMvR",
//! ],
//! // Optional list of "multi address, verbosity" of telemetry endpoints.
//! // The verbosity goes from `0` to `9`. With `0` being the mode with the lowest verbosity.
//! "telemetryEndpoints": [
//!   [
//!     "/dns/telemetry.polkadot.io/tcp/443/x-parity-wss/%2Fsubmit%2F",
//!     0
//!   ]
//! ],
//! // Optional networking protocol id that identifies the chain.
//! "protocolId": "fir9",
//! // Optional fork id. Should most likely be left empty.
//! // Can be used to signal a fork on the network level when two chains have the
//! // same genesis hash.
//! "forkId": "random_fork",
//! // Custom properties.
//! "properties": {
//!   "tokenDecimals": 15,
//!   "tokenSymbol": "FIR"
//! },
//! // Deprecated field. Should be ignored.
//! "consensusEngine": null,
//! // The genesis declaration of the chain.
//! //
//! // `runtime`, `raw`, `stateRootHash` denote the type of the genesis declaration.
//! //
//! // These declarations are in the following formats:
//! // - `runtime` is a `json` object that can be parsed by a compatible `GenesisConfig`. This
//! //  `GenesisConfig` is declared by a runtime and opaque to the node.
//! // - `raw` is a `json` object with two fields `top` and `children_default`. Each of these
//! //   fields is a map of `key => value`. These key/value pairs represent the genesis storage.
//! // - `stateRootHash` is a single hex encoded hash that represents the genesis hash. The hash
//! //   type depends on the hash used by the chain.
//! //
//! "genesis": { "runtime": {} },
//! /// Optional map of `block_number` to `wasm_code`.
//! ///
//! /// The given `wasm_code` will be used to substitute the on-chain wasm code starting with the
//! /// given block number until the `spec_version` on-chain changes. The given `wasm_code` should
//! /// be as close as possible to the on-chain wasm code. A substitute should be used to fix a bug
//! /// that can not be fixed with a runtime upgrade, if for example the runtime is constantly
//! /// panicking. Introducing new runtime apis isn't supported, because the node
//! /// will read the runtime version from the on-chain wasm code. Use this functionality only when
//! /// there is no other way around it and only patch the problematic bug, the rest should be done
//! /// with a on-chain runtime upgrade.
//! "codeSubstitutes": [],
//! ```
//!
//! The chain spec can be extended with other fields that are opaque to the default chain spec.
//! Specific node implementations will need to be able to deserialize these extensions.

mod chain_spec;
mod extension;

pub use chain_spec::{ChainSpec as GenericChainSpec, NoExtension};
pub use extension::{
	get_extension, get_extension_mut, Extension, Fork, Forks, GetExtension, Group,
};
pub use sc_chain_spec_derive::{ChainSpecExtension, ChainSpecGroup};

use sc_network_common::config::MultiaddrWithPeerId;
use sc_telemetry::TelemetryEndpoints;
use serde::{de::DeserializeOwned, Serialize};
use sp_core::storage::Storage;
use sp_runtime::BuildStorage;

/// The type of a chain.
///
/// This can be used by tools to determine the type of a chain for displaying
/// additional information or enabling additional features.
#[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq, Clone)]
pub enum ChainType {
	/// A development chain that runs mainly on one node.
	Development,
	/// A local chain that runs locally on multiple nodes for testing purposes.
	Local,
	/// A live chain.
	Live,
	/// Some custom chain type.
	Custom(String),
}

impl Default for ChainType {
	fn default() -> Self {
		Self::Live
	}
}

/// Arbitrary properties defined in chain spec as a JSON object
pub type Properties = serde_json::map::Map<String, serde_json::Value>;

/// A set of traits for the runtime genesis config.
pub trait RuntimeGenesis: Serialize + DeserializeOwned + BuildStorage {}
impl<T: Serialize + DeserializeOwned + BuildStorage> RuntimeGenesis for T {}

/// Common interface of a chain specification.
pub trait ChainSpec: BuildStorage + Send + Sync {
	/// Spec name.
	fn name(&self) -> &str;
	/// Spec id.
	fn id(&self) -> &str;
	/// Type of the chain.
	fn chain_type(&self) -> ChainType;
	/// A list of bootnode addresses.
	fn boot_nodes(&self) -> &[MultiaddrWithPeerId];
	/// Telemetry endpoints (if any)
	fn telemetry_endpoints(&self) -> &Option<TelemetryEndpoints>;
	/// Network protocol id.
	fn protocol_id(&self) -> Option<&str>;
	/// Optional network fork identifier. `None` by default.
	fn fork_id(&self) -> Option<&str>;
	/// Additional loosly-typed properties of the chain.
	///
	/// Returns an empty JSON object if 'properties' not defined in config
	fn properties(&self) -> Properties;
	/// Returns a reference to the defined chain spec extensions.
	fn extensions(&self) -> &dyn GetExtension;
	/// Returns a mutable reference to the defined chain spec extensions.
	fn extensions_mut(&mut self) -> &mut dyn GetExtension;
	/// Add a bootnode to the list.
	fn add_boot_node(&mut self, addr: MultiaddrWithPeerId);
	/// Return spec as JSON.
	fn as_json(&self, raw: bool) -> Result<String, String>;
	/// Return StorageBuilder for this spec.
	fn as_storage_builder(&self) -> &dyn BuildStorage;
	/// Returns a cloned `Box<dyn ChainSpec>`.
	fn cloned_box(&self) -> Box<dyn ChainSpec>;
	/// Set the storage that should be used by this chain spec.
	///
	/// This will be used as storage at genesis.
	fn set_storage(&mut self, storage: Storage);
	/// Returns code substitutes that should be used for the on chain wasm.
	fn code_substitutes(&self) -> std::collections::BTreeMap<String, Vec<u8>>;
}

impl std::fmt::Debug for dyn ChainSpec {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "ChainSpec(name = {:?}, id = {:?})", self.name(), self.id())
	}
}
