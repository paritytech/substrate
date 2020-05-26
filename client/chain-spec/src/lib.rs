// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Substrate chain configurations.
//!
//! This crate contains structs and utilities to declare
//! a runtime-specific configuration file (a.k.a chain spec).
//!
//! Basic chain spec type containing all required parameters is
//! [`ChainSpec`](./struct.ChainSpec.html). It can be extended with
//! additional options that contain configuration specific to your chain.
//! Usually the extension is going to be an amalgamate of types exposed
//! by Substrate core modules. To allow the core modules to retrieve
//! their configuration from your extension you should use `ChainSpecExtension`
//! macro exposed by this crate.
//!
//! ```rust
//! use std::collections::HashMap;
//! use serde::{Serialize, Deserialize};
//! use sc_chain_spec::{GenericChainSpec, ChainSpecExtension};
//!
//! #[derive(Clone, Debug, Serialize, Deserialize, ChainSpecExtension)]
//! pub struct MyExtension {
//!		pub known_blocks: HashMap<u64, String>,
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
//! use serde::{Serialize, Deserialize};
//! use sc_chain_spec::{Forks, ChainSpecGroup, ChainSpecExtension, GenericChainSpec};
//!
//! #[derive(Clone, Debug, Serialize, Deserialize, ChainSpecGroup)]
//! pub struct ClientParams {
//!		max_block_size: usize,
//!		max_extrinsic_size: usize,
//! }
//!
//! #[derive(Clone, Debug, Serialize, Deserialize, ChainSpecGroup)]
//! pub struct PoolParams {
//!		max_transaction_size: usize,
//! }
//!
//! #[derive(Clone, Debug, Serialize, Deserialize, ChainSpecGroup, ChainSpecExtension)]
//! pub struct Extension {
//!		pub client: ClientParams,
//!		pub pool: PoolParams,
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
//!		max_block_size: usize,
//!		max_extrinsic_size: usize,
//! }
//!
//! #[derive(Clone, Debug, Serialize, Deserialize, ChainSpecGroup)]
//! pub struct PoolParams {
//!		max_transaction_size: usize,
//! }
//!
//! #[derive(Clone, Debug, Serialize, Deserialize, ChainSpecExtension)]
//! pub struct Extension {
//!		pub client: ClientParams,
//!		#[forks]
//!		pub pool: Forks<u64, PoolParams>,
//! }
//!
//! pub type MyChainSpec<G> = GenericChainSpec<G, Extension>;
//! ```

mod chain_spec;
mod extension;

pub use chain_spec::{ChainSpec as GenericChainSpec, NoExtension};
pub use extension::{Group, Fork, Forks, Extension, GetExtension, get_extension};
pub use sc_chain_spec_derive::{ChainSpecExtension, ChainSpecGroup};
pub use sp_chain_spec::{Properties, ChainType};

use serde::{Serialize, de::DeserializeOwned};
use sp_runtime::BuildStorage;
use sc_network::config::MultiaddrWithPeerId;
use sc_telemetry::TelemetryEndpoints;
use sp_core::storage::Storage;

/// A set of traits for the runtime genesis config.
pub trait RuntimeGenesis: Serialize + DeserializeOwned + BuildStorage {}
impl<T: Serialize + DeserializeOwned + BuildStorage> RuntimeGenesis for T {}

/// Common interface of a chain specification.
pub trait ChainSpec: BuildStorage + Send {
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
	/// Additional loosly-typed properties of the chain.
	///
	/// Returns an empty JSON object if 'properties' not defined in config
	fn properties(&self) -> Properties;
	/// Returns a reference to defined chain spec extensions.
	fn extensions(&self) -> &dyn GetExtension;
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
}
