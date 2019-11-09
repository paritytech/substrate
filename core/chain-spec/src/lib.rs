// Copyright 2019 Parity Technologies (UK) Ltd.
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
//! use substrate_chain_spec::{ChainSpec, ChainSpecExtension};
//!
//! #[derive(Clone, Debug, Serialize, Deserialize, ChainSpecExtension)]
//! pub struct MyExtension {
//!		pub known_blocks: HashMap<u64, String>,
//! }
//!
//! pub type MyChainSpec<G> = ChainSpec<G, MyExtension>;
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
//! use substrate_chain_spec::{Forks, ChainSpec, ChainSpecGroup, ChainSpecExtension};
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
//! pub type MyChainSpec1<G> = ChainSpec<G, Forks<BlockNumber, ClientParams>>;
//!
//! /// A chain spec supporting forkable `Extension`.
//! pub type MyChainSpec2<G> = ChainSpec<G, Forks<BlockNumber, Extension>>;
//! ```
//!
//! It's also possible to have a set of parameters that is allowed to change
//! with block numbers (i.e. is forkable), and another set that is not subject to changes.
//! This is also possible by declaring an extension that contains `Forks` within it.
//!
//!
//! ```rust
//! use serde::{Serialize, Deserialize};
//! use substrate_chain_spec::{Forks, ChainSpec, ChainSpecGroup, ChainSpecExtension};
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
//! pub type MyChainSpec<G> = ChainSpec<G, Extension>;
//! ```


mod chain_spec;
mod extension;

pub use chain_spec::{ChainSpec, Properties, NoExtension};
pub use extension::{Group, Fork, Forks, Extension};
pub use substrate_chain_spec_derive::{ChainSpecExtension, ChainSpecGroup};

use serde::{Serialize, de::DeserializeOwned};
use sr_primitives::BuildStorage;

/// A set of traits for the runtime genesis config.
pub trait RuntimeGenesis: Serialize + DeserializeOwned + BuildStorage {}
impl<T: Serialize + DeserializeOwned + BuildStorage> RuntimeGenesis for T {}
