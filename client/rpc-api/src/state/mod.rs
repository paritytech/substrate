// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Substrate state API.

pub mod error;
pub mod helpers;

use self::error::FutureResult;
use jsonrpc_core::Result as RpcResult;
use jsonrpc_derive::rpc;
use jsonrpc_pubsub::{typed::Subscriber, SubscriptionId};
use sp_core::{
	storage::{StorageChangeSet, StorageData, StorageKey},
	Bytes,
};
use sp_version::RuntimeVersion;

pub use self::{gen_client::Client as StateClient, helpers::ReadProof};

/// Substrate state API
#[rpc]
pub trait StateApi<Hash> {
	/// RPC Metadata
	type Metadata;

	/// Call a contract at a block's state.
	#[rpc(name = "state_call", alias("state_callAt"))]
	fn call(&self, name: String, bytes: Bytes, hash: Option<Hash>) -> FutureResult<Bytes>;

	/// DEPRECATED: Please use `state_getKeysPaged` with proper paging support.
	/// Returns the keys with prefix, leave empty to get all the keys.
	#[rpc(name = "state_getKeys")]
	fn storage_keys(&self, prefix: StorageKey, hash: Option<Hash>)
		-> FutureResult<Vec<StorageKey>>;

	/// Returns the keys with prefix, leave empty to get all the keys
	#[rpc(name = "state_getPairs")]
	fn storage_pairs(
		&self,
		prefix: StorageKey,
		hash: Option<Hash>,
	) -> FutureResult<Vec<(StorageKey, StorageData)>>;

	/// Returns the keys with prefix with pagination support.
	/// Up to `count` keys will be returned.
	/// If `start_key` is passed, return next keys in storage in lexicographic order.
	#[rpc(name = "state_getKeysPaged", alias("state_getKeysPagedAt"))]
	fn storage_keys_paged(
		&self,
		prefix: Option<StorageKey>,
		count: u32,
		start_key: Option<StorageKey>,
		hash: Option<Hash>,
	) -> FutureResult<Vec<StorageKey>>;

	/// Returns a storage entry at a specific block's state.
	#[rpc(name = "state_getStorage", alias("state_getStorageAt"))]
	fn storage(&self, key: StorageKey, hash: Option<Hash>) -> FutureResult<Option<StorageData>>;

	/// Returns the hash of a storage entry at a block's state.
	#[rpc(name = "state_getStorageHash", alias("state_getStorageHashAt"))]
	fn storage_hash(&self, key: StorageKey, hash: Option<Hash>) -> FutureResult<Option<Hash>>;

	/// Returns the size of a storage entry at a block's state.
	#[rpc(name = "state_getStorageSize", alias("state_getStorageSizeAt"))]
	fn storage_size(&self, key: StorageKey, hash: Option<Hash>) -> FutureResult<Option<u64>>;

	/// Returns the runtime metadata as an opaque blob.
	#[rpc(name = "state_getMetadata")]
	fn metadata(&self, hash: Option<Hash>) -> FutureResult<Bytes>;

	/// Get the runtime version.
	#[rpc(name = "state_getRuntimeVersion", alias("chain_getRuntimeVersion"))]
	fn runtime_version(&self, hash: Option<Hash>) -> FutureResult<RuntimeVersion>;

	/// Query historical storage entries (by key) starting from a block given as the second
	/// parameter.
	///
	/// NOTE This first returned result contains the initial state of storage for all keys.
	/// Subsequent values in the vector represent changes to the previous state (diffs).
	#[rpc(name = "state_queryStorage")]
	fn query_storage(
		&self,
		keys: Vec<StorageKey>,
		block: Hash,
		hash: Option<Hash>,
	) -> FutureResult<Vec<StorageChangeSet<Hash>>>;

	/// Query storage entries (by key) starting at block hash given as the second parameter.
	#[rpc(name = "state_queryStorageAt")]
	fn query_storage_at(
		&self,
		keys: Vec<StorageKey>,
		at: Option<Hash>,
	) -> FutureResult<Vec<StorageChangeSet<Hash>>>;

	/// Returns proof of storage entries at a specific block's state.
	#[rpc(name = "state_getReadProof")]
	fn read_proof(
		&self,
		keys: Vec<StorageKey>,
		hash: Option<Hash>,
	) -> FutureResult<ReadProof<Hash>>;

	/// New runtime version subscription
	#[pubsub(
		subscription = "state_runtimeVersion",
		subscribe,
		name = "state_subscribeRuntimeVersion",
		alias("chain_subscribeRuntimeVersion")
	)]
	fn subscribe_runtime_version(
		&self,
		metadata: Self::Metadata,
		subscriber: Subscriber<RuntimeVersion>,
	);

	/// Unsubscribe from runtime version subscription
	#[pubsub(
		subscription = "state_runtimeVersion",
		unsubscribe,
		name = "state_unsubscribeRuntimeVersion",
		alias("chain_unsubscribeRuntimeVersion")
	)]
	fn unsubscribe_runtime_version(
		&self,
		metadata: Option<Self::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool>;

	/// New storage subscription
	#[pubsub(subscription = "state_storage", subscribe, name = "state_subscribeStorage")]
	fn subscribe_storage(
		&self,
		metadata: Self::Metadata,
		subscriber: Subscriber<StorageChangeSet<Hash>>,
		keys: Option<Vec<StorageKey>>,
	);

	/// Unsubscribe from storage subscription
	#[pubsub(subscription = "state_storage", unsubscribe, name = "state_unsubscribeStorage")]
	fn unsubscribe_storage(
		&self,
		metadata: Option<Self::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool>;

	/// The `state_traceBlock` RPC provides a way to trace the re-execution of a single
	/// block, collecting Spans and Events from both the client and the relevant WASM runtime.
	/// The Spans and Events are conceptually equivalent to those from the [Tracing][1] crate.
	///
	/// The structure of the traces follows that of the block execution pipeline, so meaningful
	/// interpretation of the traces requires an understanding of the Substrate chain's block
	/// execution.
	///
	/// [Link to conceptual map of trace structure for Polkadot and Kusama block execution.][2]
	///
	/// [1]: https://crates.io/crates/tracing
	/// [2]: https://docs.google.com/drawings/d/1vZoJo9jaXlz0LmrdTOgHck9_1LsfuQPRmTr-5g1tOis/edit?usp=sharing
	///
	/// ## Node requirements
	///
	/// - Fully synced archive node (i.e. a node that is not actively doing a "major" sync).
	/// - [Tracing enabled WASM runtimes](#creating-tracing-enabled-wasm-runtimes) for all runtime
	///   versions
	/// for which tracing is desired.
	///
	/// ## Node recommendations
	///
	/// - Use fast SSD disk storage.
	/// - Run node flags to increase DB read speed (i.e. `--state-cache-size`, `--db-cache`).
	///
	/// ## Creating tracing enabled WASM runtimes
	///
	/// - Checkout commit of chain version to compile with WASM traces
	/// - [diener][1] can help to peg commit of substrate to what the chain expects.
	/// - Navigate to the `runtime` folder/package of the chain
	/// - Add feature `with-tracing = ["frame-executive/with-tracing", "sp-io/with-tracing"]`
	/// under `[features]` to the `runtime` packages' `Cargo.toml`.
	/// - Compile the runtime with `cargo build --release --features with-tracing`
	/// - Tracing-enabled WASM runtime should be found in
	///   `./target/release/wbuild/{{chain}}-runtime`
	/// and be called something like `{{your_chain}}_runtime.compact.wasm`. This can be
	/// renamed/modified however you like, as long as it retains the `.wasm` extension.
	/// - Run the node with the wasm blob overrides by placing them in a folder with all your
	///   runtimes,
	/// and passing the path of this folder to your chain, e.g.:
	/// - `./target/release/polkadot --wasm-runtime-overrides /home/user/my-custom-wasm-runtimes`
	///
	/// You can also find some pre-built tracing enabled wasm runtimes in [substrate-archive][2]
	///
	/// [Source.][3]
	///
	/// [1]: https://crates.io/crates/diener
	/// [2]: https://github.com/paritytech/substrate-archive/tree/master/wasm-tracing
	/// [3]: https://github.com/paritytech/substrate-archive/wiki
	///
	/// ## RPC Usage
	///
	/// The RPC allows for two filtering mechanisms: tracing targets and storage key prefixes.
	/// The filtering of spans and events takes place after they are all collected; so while filters
	/// do not reduce time for actual block re-execution, they reduce the response payload size.
	///
	/// Note: storage events primarily come from _primitives/state-machine/src/ext.rs_.
	/// The default filters can be overridden, see the [params section](#params) for details.
	///
	/// ### `curl` example
	///
	/// ```text
	/// curl \
	/// 	-H "Content-Type: application/json" \
	/// 	-d '{"id":1, "jsonrpc":"2.0", "method": "state_traceBlock", \
	/// 		"params": ["0xb246acf1adea1f801ce15c77a5fa7d8f2eb8fed466978bcee172cc02cf64e264"]}' \
	/// 	http://localhost:9933/
	/// ```
	///
	/// ### Params
	///
	/// - `block_hash` (param index 0): Hash of the block to trace.
	/// - `targets` (param index 1): String of comma separated (no spaces) targets. Specified
	/// targets match with trace targets by prefix (i.e if a target is in the beginning
	/// of a trace target it is considered a match). If an empty string is specified no
	/// targets will be filtered out. The majority of targets correspond to Rust module names,
	/// and the ones that do not are typically "hardcoded" into span or event location
	/// somewhere in the Substrate source code. ("Non-hardcoded" targets typically come from frame
	/// support macros.)
	/// - `storage_keys` (param index 2): String of comma separated (no spaces) hex encoded
	/// (no `0x` prefix) storage keys. If an empty string is specified no events will
	/// be filtered out. If anything other than an empty string is specified, events
	/// will be filtered by storage key (so non-storage events will **not** show up).
	/// You can specify any length of a storage key prefix (i.e. if a specified storage
	/// key is in the beginning of an events storage key it is considered a match).
	/// Example: for balance tracking on Polkadot & Kusama you would likely want
	/// to track changes to account balances with the frame_system::Account storage item,
	/// which is a map from `AccountId` to `AccountInfo`. The key filter for this would be
	/// the storage prefix for the map:
	/// `26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da9`
	///
	/// Additionally you would want to track the extrinsic index, which is under the
	/// `:extrinsic_index` key. The key for this would be the aforementioned string as bytes
	/// in hex: `3a65787472696e7369635f696e646578`.
	/// The following are some resources to learn more about storage keys in substrate:
	/// [substrate storage][1], [transparent keys in substrate][2],
	/// [querying substrate storage via rpc][3].
	///
	/// [1]: https://substrate.dev/docs/en/knowledgebase/advanced/storage#storage-map-key
	/// [2]: https://www.shawntabrizi.com/substrate/transparent-keys-in-substrate/
	/// [3]: https://www.shawntabrizi.com/substrate/querying-substrate-storage-via-rpc/
	///
	/// ### Maximum payload size
	///
	/// The maximum payload size allowed is 15mb. Payloads over this size will return a
	/// object with a simple error message. If you run into issues with payload size you can
	/// narrow down the traces using a smaller set of targets and/or storage keys.
	///
	/// If you are having issues with maximum payload size you can use the flag
	/// `-lstate_tracing=trace` to get some logging during tracing.
	#[rpc(name = "state_traceBlock")]
	fn trace_block(
		&self,
		block: Hash,
		targets: Option<String>,
		storage_keys: Option<String>,
	) -> FutureResult<sp_rpc::tracing::TraceBlockResponse>;
}
