// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! # Substrate
//!
//! Substrate is a Rust framework for building blockchains in a modular and extensible way. While in
//! itself un-opinionated, it is the main engine behind the Polkadot ecosystem.
//!
//! [![github]](https://github.com/paritytech/substrate/) - [![polkadot]](https://polkadot.network)
//!
//! This crate in itself does not contain any code and is just meant ot be a documentation hub for
//! substrate-based crates.
//!
//! ## Overview
//!
//! Substrate approaches blockchain development with an acknowledgement of a few self-evident
//! truths:
//!
//! 1. Society and technology evolves.
//! 2. Humans are fallible.
//!
//! This, specifically, makes the task of designing a correct, safe and long-lasting blockchain
//! system hard.
//!
//! Nonetheless, in order to achieve this goal, substrate embraces the following:
//!
//! 1. Use of **Rust** as a modern, and safe programming language, which limits human error through
//!    various means, most notably memory safety.
//! 2. Substrate is written from the ground-up with a generic, modular and extensible design. This
//!    ensures that software components can be easily swapped and upgraded. Examples of this is
//!    multiple consensus mechanisms provided by Substrate, as listed below.
//! 3. Lastly, the final blockchain system created with the above properties needs to be
//!    upgradeable. In order to achieve this, Substrate is designed as a meta-protocol, whereby the
//!    application logic of the blockchain (called "Runtime") is encoded as a Wasm blob, and is
//!    stored onchain. The rest of the system (called "Client") acts as the executor of the Wasm
//!    blob.
//!
//! In essence, the meta-protocol of all Substrate based chains is the "Runtime as Wasm blob"
//! accord. This enables the Runtime to become inherently upgradeable (without forks). The upgrade
//! is merely a matter of the Wasm blob being changed in the chain state, which is, in principle,
//! same as updating an account's balance.
//!
//! To learn more about the substrate architecture using some visuals, see [`substrate_diagram`].
//!
//! `FRAME`, Substrate's default runtime development library takes the above even further by
//! embracing a declarative programming model whereby correctness is enhanced and the system is
//! highly configurable through parameterization.
//!
//! All in all, this design enables all substrate-based chains to achieve forkless, self-enacting
//! upgrades out of the box. Combined with governance abilities that are shipped with `FRAME`, this
//! enables a chain to survive the test of time.
//!
//! ## How to Get Stared
//!
//! Most developers want to leave the client side code as-is, and focus on the runtime. To do so,
//! look into the [`frame_support`] crate, which is the entry point crate into runtime development
//! with FRAME.
//!
//! > Side note, it is entirely possible to craft a substrate-based runtime without FRAME, an
//! > example of which can be found [here](https://github.com/JoshOrndorff/frameless-node-template).
//!
//! In more broad terms, the following avenues exist into developing with substrate:
//!
//! * **Templates**: A number of substrate-based templates exist and they can be used for various
//!   purposes, with zero to little additional code needed. All of these templates contain runtimes
//!   that are highly configurable and are likely suitable for basic needs.
//! * `FRAME`: If need, one can customize that runtime even further, by using `FRAME` and developing
//!   custom modules.
//! * **Core**: To the contrary, some developers may want to customize the client side software to
//!   achieve novel goals such as a new consensus engine, or a new database backend. While
//!   Substrate's main configurability is in the runtime, the client is also highly generic and can
//!   be customized to a great extent.
//!
//! ## Structure
//!
//! Substrate is a massive cargo workspace with hundreds of crates, therefore it is useful to know
//! how to navigate its crates.
//!
//! In broad terms, it is divided into three categories:
//!
//! * `sc-*` (short for *substrate-client*) crates, located under `./client` folder. These are all
//!   the client crates. Notable examples are crates such as [`sc-network`], various consensus
//!   crates, [`sc-rpc-api`] and [`sc-client-db`], all of which are expected to reside in the client
//!   side.
//! * `sp-*` (short for *substrate-primitives*) crates, located under `./primitives` folder. These
//!   are the traits that glue the client and runtime together, but are not opinionated about what
//!   framework is using for building the runtime. Notable examples are [`sp-api`] and [`sp-io`],
//!   which form the communication bridge between the client and runtime, as explained in
//!   [`substrate_diagram`].
//! * `pallet-*` and `frame-*` crates, located under `./frame` folder. These are the crates related
//!   to FRAME. See [`frame_support`] for more information.
//!
//! ### Wasm Build
//!
//! Many of the Substrate crates, such as entire `sp-*`, need to compile to both Wasm (when a Wasm
//! runtime is being generated) and native (for example, when testing). To achieve this, Substrate
//! follows the convention of the Rust community, and uses a `feature = "std"` to signify that a
//!  crate is being built with the standard library, and is built for native. Otherwise, it is built
//!  for `no_std`.
//!
//! This can be summarized in `#![cfg_attr(not(feature = "std"), no_std)]`, which you can often find
//! in any Substrate-based runtime.
//!
//! Substrate-based runtimes use [`substrate-wasm-builder`] in their `build.rs` to automatically
//! build their Wasm files as a part of normal build commandsOnce built, the wasm file is placed in
//! `./target/{debug|release}/wbuild/{runtime_name}.wasm`.
//!
//! ### Binaries
//!
//! Multiple binaries are shipped with substrate, the most important of which are located in the
//! `./bin` folder.
//!
//! * [`node`] is an extensive substrate node that contains the superset of all runtime and client
//!   side features. The corresponding runtime, called [`kitchensink_runtime`] contains all of the
//!   modules that are provided with `FRAME`. This node and runtime is only used for testing and
//!   demonstration.
//!     * [`chain-spec-builder`]: Utility to build more detailed chain-specs for the aforementioned
//!       node. Other projects typically contain a `build-spec` subcommand that does the same.
//! * [`node-template`]: a template node that contains a minimal set of features and can act as a
//!   starting point of a project.
//! * [`subkey`]: Substrate's key management utility.
//!
//! ### Anatomy of a Binary Crate
//!
//! From the above, [`node`] and [`node-template`] are essentially blueprints of a substrate-based
//! project, as the name of the latter is implying. Each substrate-based project typically contains
//! the following:
//!
//! * Under `./runtime`, a `./runtime/src/lib.rs` which is the top level runtime amalgamator file.
//!   This file typically contains the [`frame_support::construct_runtime`] macro, which is the
//!   final definition of a runtime.
//!
//! * Under `./node`, a `main.rs`, which is the point, and a `./service.rs`, which contains all the
//!   client side components. Skimming this file yields an overview of the networking, database,
//!   consensus and similar client side components.
//!
//! > The above two are conventions, not rules.
//!
//! ## Parachain?
//!
//! As noted above, Substrate is the main engine behind the Polkadot ecosystem. One of the ways
//! through which Polkadot can be utilized is by building "parachains", blockchains that are
//! connected to Polkadot's shared security.
//!
//! To build a parachain, one could use [`Cumulus`](https://github.com/paritytech/cumulus/), the
//! library on top of Substrate, empowering any substrate-based chain to be a Polkadot parachain.
//!
//! ## Where To Go Next?
//!
//! Additional noteworthy crates within substrate:
//!
//! - RPC APIs of a Substrate node: [`sc-rpc-api`]/[`sc-rpc`]
//! - CLI Options of a Substrate node: [`sc-cli`]
//! - All of the consensus related crates provided by Substrate:
//!     - [`sc-consensus-aura`]
//!     - [`sc-consensus-babe`]
//!     - [`sc-consensus-grandpa`]
//!     - [`sc-consensus-beefy`]
//!     - [`sc-consensus-manual-seal`]
//!     - [`sc-consensus-pow`]
//!
//! Additional noteworthy external resources:
//!
//! - [Substrate Developer Hub](https://substrate.dev)
//! - [Parity Tech's Documentation Hub](https://paritytech.github.io/)
//! - [Frontier: Substrate's Ethereum Compatibility Library](https://paritytech.github.io/frontier/)
//! - [Polkadot Wiki](https://wiki.polkadot.network/en/)
//!
//! Notable upstream crates:
//!
//! - [`parity-scale-codec`](https://github.com/paritytech/parity-scale-codec)
//! - [`parity-db`](https://github.com/paritytech/parity-db)
//! - [`trie`](https://github.com/paritytech/trie)
//! - [`parity-common`](https://github.com/paritytech/parity-common)
//!
//! Templates:
//!
//! - classic [`substrate-node-template`](https://github.com/substrate-developer-hub/substrate-node-template)
//! - classic [cumulus-parachain-template](https://github.com/substrate-developer-hub/substrate-parachain-template)
//! - [`extended-parachain-template`](https://github.com/paritytech/extended-parachain-template)
//! - [`frontier-parachain-template`](https://github.com/paritytech/frontier-parachain-template)
//!
//! [polkadot]:
//!     https://img.shields.io/badge/polkadot-E6007A?style=for-the-badge&logo=polkadot&logoColor=white
//! [github]:
//!     https://img.shields.io/badge/github-8da0cb?style=for-the-badge&labelColor=555555&logo=github
//! [`sp-io`]: ../sp_io/index.html
//! [`sp-api`]: ../sp_api/index.html
//! [`sp-api`]: ../sp_api/index.html
//! [`sc-client-db`]: ../sc_client_db/index.html
//! [`sc-network`]: ../sc_network/index.html
//! [`sc-rpc-api`]: ../sc_rpc_api/index.html
//! [`sc-rpc`]: ../sc_rpc/index.html
//! [`sc-cli`]: ../sc_cli/index.html
//! [`sc-consensus-aura`]: ../sc_consensus_aura/index.html
//! [`sc-consensus-babe`]: ../sc_consensus_babe/index.html
//! [`sc-consensus-grandpa`]: ../sc_consensus_grandpa/index.html
//! [`sc-consensus-beefy`]: ../sc_consensus_beefy/index.html
//! [`sc-consensus-manual-seal`]: ../sc_consensus_manual_seal/index.html
//! [`sc-consensus-pow`]: ../sc_consensus_pow/index.html
//! [`node`]: ../node_cli/index.html
//! [`node-template`]: ../node_template/index.html
//! [`kitchensink_runtime`]: ../kitchensink_runtime/index.html
//! [`subkey`]: ../subkey/index.html
//! [`chain-spec-builder`]: ../chain_spec_builder/index.html
//! [`substrate-wasm-builder`]: https://crates.io/crates/substrate-wasm-builder

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(rustdoc::private_intra_doc_links)]

#[cfg_attr(doc, aquamarine::aquamarine)]
/// In this module, we explore substrate at a more depth. First, let's establish substrate being
/// divided into a client and runtime.
///
/// ```mermaid
/// graph TB
/// subgraph Substrate
/// 	direction LR
/// 	subgraph Client
/// 	end
/// 	subgraph Runtime
/// 	end
/// end
/// ```
///
/// The client and the runtime of course need to communicate. This is done through two concepts:
///
/// 1. Host functions: a way for the (Wasm) runtime to talk to the client. All host functions are
///    defined in [`sp-io`]. For example, [`sp-io::storage`] are the set of host functions that
///    allow the runtime to read and write data to the on-chain state.
/// 2. Runtime APIs: a way for the client to talk to the Wasm runtime. Runtime APIs are defined
///    using macros and utilities in [`sp-api`]. For example, [`sp-api::Core`] is the most basic
///    runtime API that any blockchain must implement in order to be able to (re) execute blocks.
///
/// ```mermaid
/// graph TB
/// subgraph Substrate
/// 	direction LR
/// 	subgraph Client
/// 	end
/// 	subgraph Runtime
/// 	end
/// 	Client --runtime-api--> Runtime
/// 	Runtime --host-functions--> Client
/// end
/// ```
///
/// Finally, let's expand the diagram a bit further and look at the internals of each component:
///
/// ```mermaid
/// graph TB
/// subgraph Substrate
/// 	direction LR
/// 	subgraph Client
/// 		Database
/// 		Networking
/// 		Consensus
/// 	end
/// 	subgraph Runtime
/// 		subgraph FRAME
/// 			direction LR
/// 			Governance
/// 			Currency
/// 			Staking
/// 			Identity
/// 		end
/// 	end
/// 	Client --runtime-api--> Runtime
/// 	Runtime --host-functions--> Client
/// end
/// ```
///
/// As noted the runtime contains all of the application specific logic of the blockchain. This is
/// usually written with `FRAME`. The client, on the other hand, contains reusable and generic
/// components that are not specific to one single blockchain, such as networking, database, and the
/// consensus engine.
///
/// [`sp-io`]: ../../sp_io/index.html
/// [`sp-api`]: ../../sp_api/index.html
/// [`sp-io::storage`]: ../../sp_io/storage/index.html
/// [`sp-api::Core`]: ../../sp_api/trait.Core.html
pub mod substrate_diagram {}
