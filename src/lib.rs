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
//! Substrate approaches blockchain development with a focus on **safety**, **correctness**, and
//! **upgradeability**.
//!
//! **Safety** is acquired through a use of Rust, a modern language empowering everyone to build
//! reliable and efficient software.
//!
//! **Correctness** is ensured through a rich type system enforcing semantic guarantees. This is
//! more relevant in `FRAME`, the companion framework of Substrate for writing the business logic of
//! your blockchain, also known as the "runtime" or "state transition function".
//!
//! Finally, **upgradeability** is achieved through a meta-protocol design, whereby the entire
//! application logic of the blockchain (the _Runtime_) is encoded as a Wasm module, and is stored
//! on-chain. Other than the runtime, the rest of the system is called the "client" software, which
//! is a native binary capable of doing all the redundant, non-application-specific work, such as
//! networking, consensus, and database management.
//!
//! To learn more about the substrate architecture using some visuals, see [`substrate_diagram`].
//!
//! All in all, this design enables all substrate-based chains to achieve forkless, self-enacting
//! upgrades out of the box. Combined with governance abilities that are shipped with `FRAME`, this
//! enables a chain to always evolve.
//!
//! ## How to Get Stared
//!
//! Most developers want to leave the client side code as-is, and focus on the runtime. To do so,
//! look into the [`frame_support`] crate, which is the entry point crate into runtime development.
//!
//! > Side note, it is entirely possible to craft a substrate-based runtime without FRAME, an
//! > example of which can be found here.
//!
//! In more broad terms, two common avenues exist into substrate:
//!
//! 1. Starting with templates: A number of substrate-based templates exist and they can be used for
//!    various purposes, with zero to little additional code needed. All of these templates contain
//!    runtimes that are highly configurable and are likely suitable for basic needs.
//! 2. Customizing the client: To the contrary, some developers may want to customize the client
//!    side software to achieve novel goals such as a new consensus engine, or a new database
//!    backend. While Substrate's main configurability is in the runtime, the client is also highly
//!    generic and can be customized to a great extent.
//!
//! ## Structure
//!
//! Substrate is a massive cargo workspace with hundreds of crates, therefore it is useful to know
//! how to navigate its crates.
//!
//! In broad terms, it is divided into three categories:
//!
//! * `sc-*` (short for *substrate-client*) crates, located under `./client` folder. These are all
//!   the client crates. Notable examples are crates such as [`sc-network`], [`sc-consensus`] and
//!   [`sc-client-db`], all of which are expected to reside in the client side.
//! * `sp` (short for *substrate-primitives*) crates, located under `./primitives` folder. These are
//!   the traits that glue the client and runtime together, but are not opinionated about what
//!   framework is using for building the runtime. Notable examples are [`sp-api`] and [`sp-io`],
//!   which form the communication bridge between the client and runtime, as explained in
//!   [`substrate_diagram`].
//! * `pallet-*` and `frame-*` crates, located under `./frame` folder. These are the crates related
//!   to FRAME. See [`frame_support`] for more information.
//!
//! ## Additional Resources
//!
//! Additional resources to get started with substrate:
//!
//! - [Substrate Developer Hub](https://substrate.dev)
//! - [Parity Tech's Rust Docs Hub](https://paritytech.github.io/)
//! - [Polkadot Wiki](https://wiki.polkadot.network/en/)
//!
//! TODO: templates?
//! TODO: examples?
//!
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
//! [`sc-consensus`]: ../sc_consensus/index.html

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
///    defined in [`sp_io`]. For example, [`sp_io::storage`] are the set of host functions that
///    allow the runtime to read and write data to the on-chain state.
/// 2. Runtime APIs: a way for the client to talk to the Wasm runtime. Runtime APIs are defined
///    using macros and utilities in [`sp-api`]. For example, [`sp_api::Core`] is the most basic
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
/// As noted the runtime contains all of the application specific logic of the blockchain.
pub mod substrate_diagram {}
