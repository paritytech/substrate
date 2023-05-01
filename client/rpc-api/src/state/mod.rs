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

//! Substrate state API.

use jsonrpsee::{core::RpcResult, proc_macros::rpc};
use sp_core::{
	storage::{StorageChangeSet, StorageData, StorageKey},
	Bytes,
};
use sp_version::RuntimeVersion;

pub mod error;
pub mod helpers;

pub use self::helpers::ReadProof;

/// Substrate state API
#[rpc(client, server)]
pub trait StateApi<Hash> {
	/// Call a method from the runtime API at a block's state.
	#[method(name = "state_call", aliases = ["state_callAt"], blocking)]
	fn call(&self, name: String, bytes: Bytes, hash: Option<Hash>) -> RpcResult<Bytes>;

	/// Returns the keys with prefix, leave empty to get all the keys.
	#[method(name = "state_getKeys", blocking)]
	#[deprecated(since = "2.0.0", note = "Please use `getKeysPaged` with proper paging support")]
	fn storage_keys(&self, prefix: StorageKey, hash: Option<Hash>) -> RpcResult<Vec<StorageKey>>;

	/// Returns the keys with prefix, leave empty to get all the keys
	#[method(name = "state_getPairs", blocking)]
	fn storage_pairs(
		&self,
		prefix: StorageKey,
		hash: Option<Hash>,
	) -> RpcResult<Vec<(StorageKey, StorageData)>>;

	/// Returns the keys with prefix with pagination support.
	/// Up to `count` keys will be returned.
	/// If `start_key` is passed, return next keys in storage in lexicographic order.
	#[method(name = "state_getKeysPaged", aliases = ["state_getKeysPagedAt"], blocking)]
	fn storage_keys_paged(
		&self,
		prefix: Option<StorageKey>,
		count: u32,
		start_key: Option<StorageKey>,
		hash: Option<Hash>,
	) -> RpcResult<Vec<StorageKey>>;

	/// Returns a storage entry at a specific block's state.
	#[method(name = "state_getStorage", aliases = ["state_getStorageAt"], blocking)]
	fn storage(&self, key: StorageKey, hash: Option<Hash>) -> RpcResult<Option<StorageData>>;

	/// Returns the hash of a storage entry at a block's state.
	#[method(name = "state_getStorageHash", aliases = ["state_getStorageHashAt"], blocking)]
	fn storage_hash(&self, key: StorageKey, hash: Option<Hash>) -> RpcResult<Option<Hash>>;

	/// Returns the size of a storage entry at a block's state.
	#[method(name = "state_getStorageSize", aliases = ["state_getStorageSizeAt"])]
	async fn storage_size(&self, key: StorageKey, hash: Option<Hash>) -> RpcResult<Option<u64>>;

	/// Returns the runtime metadata as an opaque blob.
	#[method(name = "state_getMetadata", blocking)]
	fn metadata(&self, hash: Option<Hash>) -> RpcResult<Bytes>;

	/// Get the runtime version.
	#[method(name = "state_getRuntimeVersion", aliases = ["chain_getRuntimeVersion"], blocking)]
	fn runtime_version(&self, hash: Option<Hash>) -> RpcResult<RuntimeVersion>;

	/// Query historical storage entries (by key) starting from a block given as the second
	/// parameter.
	///
	/// NOTE: The first returned result contains the initial state of storage for all keys.
	/// Subsequent values in the vector represent changes to the previous state (diffs).
	/// WARNING: The time complexity of this query is O(|keys|*dist(block, hash)), and the
	/// memory complexity is O(dist(block, hash)) -- use with caution.
	#[method(name = "state_queryStorage", blocking)]
	fn query_storage(
		&self,
		keys: Vec<StorageKey>,
		block: Hash,
		hash: Option<Hash>,
	) -> RpcResult<Vec<StorageChangeSet<Hash>>>;

	/// Query storage entries (by key) at a block hash given as the second parameter.
	/// NOTE: Each StorageChangeSet in the result corresponds to exactly one element --
	/// the storage value under an input key at the input block hash.
	#[method(name = "state_queryStorageAt", blocking)]
	fn query_storage_at(
		&self,
		keys: Vec<StorageKey>,
		at: Option<Hash>,
	) -> RpcResult<Vec<StorageChangeSet<Hash>>>;

	/// Returns proof of storage entries at a specific block's state.
	#[method(name = "state_getReadProof", blocking)]
	fn read_proof(&self, keys: Vec<StorageKey>, hash: Option<Hash>) -> RpcResult<ReadProof<Hash>>;

	/// New runtime version subscription
	#[subscription(
		name = "state_subscribeRuntimeVersion" => "state_runtimeVersion",
		unsubscribe = "state_unsubscribeRuntimeVersion",
		aliases = ["chain_subscribeRuntimeVersion"],
		unsubscribe_aliases = ["chain_unsubscribeRuntimeVersion"],
		item = RuntimeVersion,
	)]
	fn subscribe_runtime_version(&self);

	/// New storage subscription
	#[subscription(
		name = "state_subscribeStorage" => "state_storage",
		unsubscribe = "state_unsubscribeStorage",
		item = StorageChangeSet<Hash>,
	)]
	fn subscribe_storage(&self, keys: Option<Vec<StorageKey>>);

	/// The `traceBlock` RPC provides a way to trace the re-execution of a single
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
	/// - Get tracing spans and events
	/// ```text
	/// curl \
	/// 	-H "Content-Type: application/json" \
	/// 	-d '{"id":1, "jsonrpc":"2.0", "method": "state_traceBlock", \
	/// 		"params": ["0xb246acf1adea1f801ce15c77a5fa7d8f2eb8fed466978bcee172cc02cf64e264", "pallet,frame,state", "", ""]}' \
	/// 	http://localhost:9933/
	/// ```
	///
	/// - Get tracing events with all `storage_keys`
	/// ```text
	/// curl \
	/// 	-H "Content-Type: application/json" \
	/// 	-d '{"id":1, "jsonrpc":"2.0", "method": "state_traceBlock", \
	/// 		"params": ["0xb246acf1adea1f801ce15c77a5fa7d8f2eb8fed466978bcee172cc02cf64e264", "state", "", ""]}' \
	/// 	http://localhost:9933/
	/// ```
	///
	/// - Get tracing events with `storage_keys` ('f0c365c3cf59d671eb72da0e7a4113c4')
	/// ```text
	/// curl \
	/// 	-H "Content-Type: application/json" \
	/// 	-d '{"id":1, "jsonrpc":"2.0", "method": "state_traceBlock", \
	/// 		"params": ["0xb246acf1adea1f801ce15c77a5fa7d8f2eb8fed466978bcee172cc02cf64e264", "state", "f0c365c3cf59d671eb72da0e7a4113c4", ""]}' \
	/// 	http://localhost:9933/
	/// ```
	///
	/// - Get tracing events with `storage_keys` ('f0c365c3cf59d671eb72da0e7a4113c4') and method
	///   ('Put')
	/// ```text
	/// curl \
	/// 	-H "Content-Type: application/json" \
	/// 	-d '{"id":1, "jsonrpc":"2.0", "method": "state_traceBlock", \
	/// 		"params": ["0xb246acf1adea1f801ce15c77a5fa7d8f2eb8fed466978bcee172cc02cf64e264", "state", "f0c365c3cf59d671eb72da0e7a4113c4", "Put"]}' \
	/// 	http://localhost:9933/
	/// ```
	///
	/// - Get tracing events with all `storage_keys` and method ('Put')
	/// ```text
	/// curl \
	/// 	-H "Content-Type: application/json" \
	/// 	-d '{"id":1, "jsonrpc":"2.0", "method": "state_traceBlock", \
	/// 		"params": ["0xb246acf1adea1f801ce15c77a5fa7d8f2eb8fed466978bcee172cc02cf64e264", "state", "", "Put"]}' \
	/// 	http://localhost:9933/
	/// ```
	///
	/// ### Params
	///
	/// - `block` (param index 0): Hash of the block to trace.
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
	/// - `methods` (param index 3): String of comma separated (no spaces) tracing event method.
	/// If an empty string is specified no events will be filtered out. If anything other than
	/// an empty string is specified, events will be filtered by method (so non-method events will
	/// **not** show up).
	///
	/// Additionally you would want to track the extrinsic index, which is under the
	/// `:extrinsic_index` key. The key for this would be the aforementioned string as bytes
	/// in hex: `3a65787472696e7369635f696e646578`.
	/// The following are some resources to learn more about storage keys in substrate:
	/// [substrate storage][1], [transparent keys in substrate][2],
	/// [querying substrate storage via rpc][3].
	///
	/// [1]: https://docs.substrate.io/main-docs/fundamentals/state-transitions-and-storage/
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
	/// `-ltracing=trace` to get some logging during tracing.
	#[method(name = "state_traceBlock", blocking)]
	fn trace_block(
		&self,
		block: Hash,
		targets: Option<String>,
		storage_keys: Option<String>,
		methods: Option<String>,
	) -> RpcResult<sp_rpc::tracing::TraceBlockResponse>;
}
