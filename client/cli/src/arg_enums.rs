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

//! Definitions of [`ValueEnum`] types.

use clap::ValueEnum;

/// The instantiation strategy to use in compiled mode.
#[derive(Debug, Clone, Copy, ValueEnum)]
#[value(rename_all = "kebab-case")]
pub enum WasmtimeInstantiationStrategy {
	/// Pool the instances to avoid initializing everything from scratch
	/// on each instantiation. Use copy-on-write memory when possible.
	PoolingCopyOnWrite,

	/// Recreate the instance from scratch on every instantiation.
	/// Use copy-on-write memory when possible.
	RecreateInstanceCopyOnWrite,

	/// Pool the instances to avoid initializing everything from scratch
	/// on each instantiation.
	Pooling,

	/// Recreate the instance from scratch on every instantiation. Very slow.
	RecreateInstance,

	/// Legacy instance reuse mechanism. DEPRECATED. Will be removed in the future.
	///
	/// Should only be used in case of encountering any issues with the new default
	/// instantiation strategy.
	LegacyInstanceReuse,
}

/// The default [`WasmtimeInstantiationStrategy`].
pub const DEFAULT_WASMTIME_INSTANTIATION_STRATEGY: WasmtimeInstantiationStrategy =
	WasmtimeInstantiationStrategy::PoolingCopyOnWrite;

/// How to execute Wasm runtime code.
#[derive(Debug, Clone, Copy, ValueEnum)]
#[value(rename_all = "kebab-case")]
pub enum WasmExecutionMethod {
	/// Uses an interpreter which now is deprecated.
	#[clap(name = "interpreted-i-know-what-i-do")]
	Interpreted,
	/// Uses a compiled runtime.
	Compiled,
}

impl std::fmt::Display for WasmExecutionMethod {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Interpreted => write!(f, "Interpreted"),
			Self::Compiled => write!(f, "Compiled"),
		}
	}
}

/// Converts the execution method and instantiation strategy command line arguments
/// into an execution method which can be used internally.
pub fn execution_method_from_cli(
	execution_method: WasmExecutionMethod,
	instantiation_strategy: WasmtimeInstantiationStrategy,
) -> sc_service::config::WasmExecutionMethod {
	if let WasmExecutionMethod::Interpreted = execution_method {
		log::warn!(
			"`interpreted-i-know-what-i-do` is deprecated and will be removed in the future. Defaults to `compiled` execution mode."
		);
	}

	sc_service::config::WasmExecutionMethod::Compiled {
		instantiation_strategy: match instantiation_strategy {
			WasmtimeInstantiationStrategy::PoolingCopyOnWrite =>
				sc_service::config::WasmtimeInstantiationStrategy::PoolingCopyOnWrite,
			WasmtimeInstantiationStrategy::RecreateInstanceCopyOnWrite =>
				sc_service::config::WasmtimeInstantiationStrategy::RecreateInstanceCopyOnWrite,
			WasmtimeInstantiationStrategy::Pooling =>
				sc_service::config::WasmtimeInstantiationStrategy::Pooling,
			WasmtimeInstantiationStrategy::RecreateInstance =>
				sc_service::config::WasmtimeInstantiationStrategy::RecreateInstance,
			WasmtimeInstantiationStrategy::LegacyInstanceReuse =>
				sc_service::config::WasmtimeInstantiationStrategy::LegacyInstanceReuse,
		},
	}
}

/// The default [`WasmExecutionMethod`].
pub const DEFAULT_WASM_EXECUTION_METHOD: WasmExecutionMethod = WasmExecutionMethod::Compiled;

#[allow(missing_docs)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, ValueEnum)]
#[value(rename_all = "kebab-case")]
pub enum TracingReceiver {
	/// Output the tracing records using the log.
	Log,
}

impl Into<sc_tracing::TracingReceiver> for TracingReceiver {
	fn into(self) -> sc_tracing::TracingReceiver {
		match self {
			TracingReceiver::Log => sc_tracing::TracingReceiver::Log,
		}
	}
}

/// The type of the node key.
#[derive(Debug, Copy, Clone, PartialEq, Eq, ValueEnum)]
#[value(rename_all = "kebab-case")]
pub enum NodeKeyType {
	/// Use ed25519.
	Ed25519,
}

/// The crypto scheme to use.
#[derive(Debug, Copy, Clone, PartialEq, Eq, ValueEnum)]
#[value(rename_all = "kebab-case")]
pub enum CryptoScheme {
	/// Use ed25519.
	Ed25519,
	/// Use sr25519.
	Sr25519,
	/// Use
	Ecdsa,
}

/// The type of the output format.
#[derive(Debug, Copy, Clone, PartialEq, Eq, ValueEnum)]
#[value(rename_all = "kebab-case")]
pub enum OutputType {
	/// Output as json.
	Json,
	/// Output as text.
	Text,
}

/// How to execute blocks
#[derive(Debug, Copy, Clone, PartialEq, Eq, ValueEnum)]
#[value(rename_all = "kebab-case")]
pub enum ExecutionStrategy {
	/// Execute with native build (if available, WebAssembly otherwise).
	Native,
	/// Only execute with the WebAssembly build.
	Wasm,
	/// Execute with both native (where available) and WebAssembly builds.
	Both,
	/// Execute with the native build if possible; if it fails, then execute with WebAssembly.
	NativeElseWasm,
}

impl Into<sc_client_api::ExecutionStrategy> for ExecutionStrategy {
	fn into(self) -> sc_client_api::ExecutionStrategy {
		match self {
			ExecutionStrategy::Native => sc_client_api::ExecutionStrategy::NativeWhenPossible,
			ExecutionStrategy::Wasm => sc_client_api::ExecutionStrategy::AlwaysWasm,
			ExecutionStrategy::Both => sc_client_api::ExecutionStrategy::Both,
			ExecutionStrategy::NativeElseWasm => sc_client_api::ExecutionStrategy::NativeElseWasm,
		}
	}
}

/// Available RPC methods.
#[allow(missing_docs)]
#[derive(Debug, Copy, Clone, PartialEq, ValueEnum)]
#[value(rename_all = "kebab-case")]
pub enum RpcMethods {
	/// Expose every RPC method only when RPC is listening on `localhost`,
	/// otherwise serve only safe RPC methods.
	Auto,
	/// Allow only a safe subset of RPC methods.
	Safe,
	/// Expose every RPC method (even potentially unsafe ones).
	Unsafe,
}

impl Into<sc_service::config::RpcMethods> for RpcMethods {
	fn into(self) -> sc_service::config::RpcMethods {
		match self {
			RpcMethods::Auto => sc_service::config::RpcMethods::Auto,
			RpcMethods::Safe => sc_service::config::RpcMethods::Safe,
			RpcMethods::Unsafe => sc_service::config::RpcMethods::Unsafe,
		}
	}
}

/// Database backend
#[derive(Debug, Clone, PartialEq, Copy, clap::ValueEnum)]
#[value(rename_all = "lower")]
pub enum Database {
	/// Facebooks RocksDB
	#[cfg(feature = "rocksdb")]
	RocksDb,
	/// ParityDb. <https://github.com/paritytech/parity-db/>
	ParityDb,
	/// Detect whether there is an existing database. Use it, if there is, if not, create new
	/// instance of ParityDb
	Auto,
	/// ParityDb. <https://github.com/paritytech/parity-db/>
	#[value(name = "paritydb-experimental")]
	ParityDbDeprecated,
}

impl Database {
	/// Returns all the variants of this enum to be shown in the cli.
	pub const fn variants() -> &'static [&'static str] {
		&[
			#[cfg(feature = "rocksdb")]
			"rocksdb",
			"paritydb",
			"paritydb-experimental",
			"auto",
		]
	}
}

/// Whether off-chain workers are enabled.
#[allow(missing_docs)]
#[derive(Debug, Clone, ValueEnum)]
#[value(rename_all = "kebab-case")]
pub enum OffchainWorkerEnabled {
	/// Always have offchain worker enabled.
	Always,
	/// Never enable the offchain worker.
	Never,
	/// Only enable the offchain worker when running as a validator (or collator, if this is a
	/// parachain node).
	WhenAuthority,
}

/// Syncing mode.
#[derive(Debug, Clone, Copy, ValueEnum, PartialEq)]
#[value(rename_all = "kebab-case")]
pub enum SyncMode {
	/// Full sync. Download end verify all blocks.
	Full,
	/// Download blocks without executing them. Download latest state with proofs.
	Fast,
	/// Download blocks without executing them. Download latest state without proofs.
	FastUnsafe,
	/// Prove finality and download the latest state.
	Warp,
}

impl Into<sc_network::config::SyncMode> for SyncMode {
	fn into(self) -> sc_network::config::SyncMode {
		match self {
			SyncMode::Full => sc_network::config::SyncMode::Full,
			SyncMode::Fast =>
				sc_network::config::SyncMode::Fast { skip_proofs: false, storage_chain_mode: false },
			SyncMode::FastUnsafe =>
				sc_network::config::SyncMode::Fast { skip_proofs: true, storage_chain_mode: false },
			SyncMode::Warp => sc_network::config::SyncMode::Warp,
		}
	}
}

/// Default value for the `--execution-syncing` parameter.
pub const DEFAULT_EXECUTION_SYNCING: ExecutionStrategy = ExecutionStrategy::Wasm;
/// Default value for the `--execution-import-block` parameter.
pub const DEFAULT_EXECUTION_IMPORT_BLOCK: ExecutionStrategy = ExecutionStrategy::Wasm;
/// Default value for the `--execution-import-block` parameter when the node is a validator.
pub const DEFAULT_EXECUTION_IMPORT_BLOCK_VALIDATOR: ExecutionStrategy = ExecutionStrategy::Wasm;
/// Default value for the `--execution-block-construction` parameter.
pub const DEFAULT_EXECUTION_BLOCK_CONSTRUCTION: ExecutionStrategy = ExecutionStrategy::Wasm;
/// Default value for the `--execution-offchain-worker` parameter.
pub const DEFAULT_EXECUTION_OFFCHAIN_WORKER: ExecutionStrategy = ExecutionStrategy::Wasm;
/// Default value for the `--execution-other` parameter.
pub const DEFAULT_EXECUTION_OTHER: ExecutionStrategy = ExecutionStrategy::Wasm;
