// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Remote Externalities
//!
//! An equivalent of `sp_io::TestExternalities` that can load its state from a remote substrate
//! based chain, or a local state snapshot file.

use codec::{Decode, Encode};
use jsonrpsee::{
	core::{client::ClientT, Error as RpcError},
	proc_macros::rpc,
	rpc_params,
	ws_client::{WsClient, WsClientBuilder},
};

use log::*;
use serde::de::DeserializeOwned;
use sp_core::{
	hashing::twox_128,
	hexdisplay::HexDisplay,
	storage::{
		well_known_keys::{is_default_child_storage_key, DEFAULT_CHILD_STORAGE_KEY_PREFIX},
		ChildInfo, ChildType, PrefixedStorageKey, StorageData, StorageKey,
	},
};
pub use sp_io::TestExternalities;
use sp_runtime::{
	traits::{Block as BlockT},
	StateVersion,
};
use std::{
	fs,
	path::{Path, PathBuf},
	sync::Arc,
};

// CHANGELOG:
// 1. `pallets` no longer has the interpretation of an empty list implying everything. If
// `hashed_prefix` and pallets are both empty, then we scrape everything. Not the biggest fan
// myself, but needed to keep things backwards compatible.
// 2. snapshot format has changed and now is a single file, and contains block hash as well.
// 3. `build_with_block_hash` can be used to build and get the eventual final block hash that
// corresponded to the state.
//

pub mod rpc_api;

type KeyValue = (StorageKey, StorageData);
type TopKeyValues = Vec<KeyValue>;
type ChildKeyValues = Vec<(ChildInfo, Vec<KeyValue>)>;

const LOG_TARGET: &str = "remote-ext";
const DEFAULT_WS_ENDPOINT: &str = "wss://rpc.polkadot.io:443";
const DEFAULT_VALUE_DOWNLOAD_THREADS: usize = 8;
const DEFAULT_VALUE_DOWNLOAD_BATCH: usize = 4096;
// NOTE: increasing this value does not seem to impact speed all that much.
const DEFAULT_KEY_DOWNLOAD_PAGE: u32 = 1000;

#[derive(Decode, Encode)]
struct Snapshot<B: BlockT> {
	block_hash: B::Hash,
	top: TopKeyValues,
	child: ChildKeyValues,
}

#[rpc(client)]
pub trait RpcApi<Hash> {
	#[method(name = "childstate_getKeys")]
	fn child_get_keys(
		&self,
		child_key: PrefixedStorageKey,
		prefix: StorageKey,
		hash: Option<Hash>,
	) -> Result<Vec<StorageKey>, RpcError>;

	#[method(name = "childstate_getStorage")]
	fn child_get_storage(
		&self,
		child_key: PrefixedStorageKey,
		prefix: StorageKey,
		hash: Option<Hash>,
	) -> Result<StorageData, RpcError>;

	#[method(name = "state_getStorage")]
	fn get_storage(&self, prefix: StorageKey, hash: Option<Hash>) -> Result<StorageData, RpcError>;

	#[method(name = "state_getKeysPaged")]
	fn get_keys_paged(
		&self,
		prefix: Option<StorageKey>,
		count: u32,
		start_key: Option<StorageKey>,
		hash: Option<Hash>,
	) -> Result<Vec<StorageKey>, RpcError>;

	#[method(name = "chain_getFinalizedHead")]
	fn finalized_head(&self) -> Result<Hash, RpcError>;
}

/// The execution mode.
#[derive(Clone)]
pub enum Mode<B: BlockT> {
	/// Online. Potentially writes to a snapshot file.
	Online(OnlineConfig<B>),
	/// Offline. Uses a state snapshot file and needs not any client config.
	Offline(OfflineConfig),
	/// Prefer using a snapshot file if it exists, else use a remote server.
	OfflineOrElseOnline(OfflineConfig, OnlineConfig<B>),
}

impl<B: BlockT> Default for Mode<B> {
	fn default() -> Self {
		Mode::Online(OnlineConfig::default())
	}
}

/// Configuration of the offline execution.
///
/// A state snapshot config must be present.
#[derive(Clone)]
pub struct OfflineConfig {
	/// The configuration of the state snapshot file to use. It must be present.
	pub state_snapshot: SnapshotConfig,
}

/// Description of the transport protocol (for online execution).
#[derive(Debug, Clone)]
pub struct Transport {
	/// Use the `URI` to open a new WebSocket connection.
	pub uri: Option<String>,
	/// Use existing WebSocket connection.
	pub remote_client: Option<Arc<WsClient>>,
}

impl Transport {
	fn as_client(&self) -> Option<&WsClient> {
		self.remote_client.as_ref().map(|x| x.as_ref())
	}

	async fn build_ws_client(uri: &str) -> Result<WsClient, &'static str> {
		log::info!(target: LOG_TARGET, "initializing remote client to {:?}", uri);
		WsClientBuilder::default()
			.max_request_body_size(u32::MAX)
			.request_timeout(std::time::Duration::from_secs(5 * 10))
			.connection_timeout(std::time::Duration::from_secs(60))
			.max_notifs_per_subscription(1024)
			.build(&uri)
			.await
			.map_err(|e| {
				log::error!(target: LOG_TARGET, "error: {:?}", e);
				"failed to build ws client"
			})
	}

	// Open a new WebSocket connection if it's not connected.
	async fn map_uri(&mut self) -> Result<(), &'static str> {
		if let Some(uri) = &self.uri {
			let ws_client = Self::build_ws_client(&uri).await?;
			self.remote_client = Some(Arc::new(ws_client));
		}

		Ok(())
	}
}

impl From<String> for Transport {
	fn from(uri: String) -> Self {
		Transport { uri: Some(uri), remote_client: None }
	}
}

impl From<&str> for Transport {
	fn from(uri: &str) -> Self {
		Transport { uri: Some(uri.to_string()), remote_client: None }
	}
}

impl From<Arc<WsClient>> for Transport {
	fn from(_: Arc<WsClient>) -> Self {
		unimplemented!("we should not allow this. any client must be first built with a uri");
	}
}

/// Configuration of the online execution.
///
/// A state snapshot config may be present and will be written to in that case.
#[derive(Clone)]
pub struct OnlineConfig<B: BlockT> {
	/// The block hash at which to get the runtime state. Will be latest finalized head if not
	/// provided.
	pub at: Option<B::Hash>,
	/// An optional state snapshot file to WRITE to, not for reading. Not written if set to `None`.
	pub state_snapshot: Option<SnapshotConfig>,
	/// The pallets to scrape. These values are hashed and added to `hashed_prefix`.
	pub pallets: Vec<String>,
	/// Transport config.
	pub transport: Transport,
	/// Lookout for child-keys, and scrape them as well if set to true.
	pub child_trie: bool,
	/// Storage entry key prefixes to be injected into the externalities. The *hashed* prefix must
	/// be given.
	pub hashed_prefixes: Vec<Vec<u8>>,
	/// Storage entry keys to be injected into the externalities. The *hashed* key must be given.
	pub hashed_keys: Vec<Vec<u8>>,
	/// The number of threads to be used while downloading values.
	pub threads: usize,
}

impl<B: BlockT> OnlineConfig<B> {
	/// Return rpc (ws) client.
	fn rpc_client(&self) -> &WsClient {
		self.transport
			.as_client()
			.expect("ws client must have been initialized by now; qed.")
	}

	fn at_expected(&self) -> B::Hash {
		self.at.expect("block at must be initialized; qed")
	}
}

impl<B: BlockT> Default for OnlineConfig<B> {
	fn default() -> Self {
		Self {
			transport: Transport::from(DEFAULT_WS_ENDPOINT),
			child_trie: true,
			at: None,
			threads: DEFAULT_VALUE_DOWNLOAD_THREADS,
			state_snapshot: None,
			pallets: Default::default(),
			hashed_keys: Default::default(),
			hashed_prefixes: Default::default(),
		}
	}
}

impl<B: BlockT> From<String> for OnlineConfig<B> {
	fn from(s: String) -> Self {
		Self { transport: s.into(), ..Default::default() }
	}
}

impl<B: BlockT> From<&str> for OnlineConfig<B> {
	fn from(s: &str) -> Self {
		Self { transport: s.to_string().into(), ..Default::default() }
	}
}

/// Configuration of the state snapshot.
#[derive(Clone)]
pub struct SnapshotConfig {
	/// The path to the snapshot file.
	pub path: PathBuf,
}

impl SnapshotConfig {
	pub fn new<P: Into<PathBuf>>(path: P) -> Self {
		Self { path: path.into() }
	}
}

impl From<String> for SnapshotConfig {
	fn from(s: String) -> Self {
		Self::new(s)
	}
}

impl Default for SnapshotConfig {
	fn default() -> Self {
		Self { path: Path::new("SNAPSHOT").into() }
	}
}

/// Builder for remote-externalities.
pub struct Builder<B: BlockT> {
	/// Custom key-pairs to be injected into the final externalities. The *hashed* keys and values
	/// must be given.
	hashed_key_values: Vec<KeyValue>,
	/// The keys that will be excluded from the final externality. The *hashed* key must be given.
	hashed_blacklist: Vec<Vec<u8>>,
	/// connectivity mode, online or offline.
	mode: Mode<B>,
	/// The state version being used.
	state_version: StateVersion,
	/// the final hash of the block who's state is set in the externalities. This is always
	/// `Some(_)` after calling `build`.
	final_state_block_hash: Option<B::Hash>,
}

// NOTE: ideally we would use `DefaultNoBound` here, but not worth bringing in frame-support for
// that.
impl<B: BlockT + DeserializeOwned> Default for Builder<B> {
	fn default() -> Self {
		Self {
			mode: Default::default(),
			hashed_key_values: Default::default(),
			hashed_blacklist: Default::default(),
			state_version: StateVersion::V1,
			final_state_block_hash: None,
		}
	}
}

// Mode methods
impl<B: BlockT + DeserializeOwned> Builder<B> {
	fn as_online(&self) -> &OnlineConfig<B> {
		match &self.mode {
			Mode::Online(config) => config,
			Mode::OfflineOrElseOnline(_, config) => config,
			_ => panic!("Unexpected mode: Online"),
		}
	}

	fn as_online_mut(&mut self) -> &mut OnlineConfig<B> {
		match &mut self.mode {
			Mode::Online(config) => config,
			Mode::OfflineOrElseOnline(_, config) => config,
			_ => panic!("Unexpected mode: Online"),
		}
	}
}

// RPC methods
impl<B: BlockT + DeserializeOwned> Builder<B> {
	async fn rpc_get_storage(
		&self,
		key: StorageKey,
		maybe_at: Option<B::Hash>,
	) -> Result<StorageData, &'static str> {
		trace!(target: LOG_TARGET, "rpc: get_storage");
		self.as_online().rpc_client().get_storage(key, maybe_at).await.map_err(|e| {
			error!(target: LOG_TARGET, "Error = {:?}", e);
			"rpc get_storage failed."
		})
	}

	/// Get the latest finalized head.
	async fn rpc_get_head(&self) -> Result<B::Hash, &'static str> {
		trace!(target: LOG_TARGET, "rpc: finalized_head");
		self.as_online().rpc_client().finalized_head().await.map_err(|e| {
			error!(target: LOG_TARGET, "Error = {:?}", e);
			"rpc finalized_head failed."
		})
	}

	/// Get all the keys at `prefix` at `hash` using the paged, safe RPC methods.
	async fn rpc_get_keys_paged(
		&self,
		prefix: StorageKey,
		at: B::Hash,
	) -> Result<Vec<StorageKey>, &'static str> {
		let mut last_key: Option<StorageKey> = None;
		let mut all_keys: Vec<StorageKey> = vec![];
		let keys = loop {
			let page = self
				.as_online()
				.rpc_client()
				.get_keys_paged(
					Some(prefix.clone()),
					DEFAULT_KEY_DOWNLOAD_PAGE,
					last_key.clone(),
					Some(at),
				)
				.await
				.map_err(|e| {
					error!(target: LOG_TARGET, "Error = {:?}", e);
					"rpc get_keys failed"
				})?;
			let page_len = page.len();

			all_keys.extend(page);

			if page_len < DEFAULT_KEY_DOWNLOAD_PAGE as usize {
				log::debug!(target: LOG_TARGET, "last page received: {}", page_len);
				break all_keys
			} else {
				let new_last_key =
					all_keys.last().expect("all_keys is populated; has .last(); qed");
				log::debug!(
					target: LOG_TARGET,
					"new total = {}, full page received: {}",
					all_keys.len(),
					HexDisplay::from(new_last_key)
				);
				last_key = Some(new_last_key.clone());
			}
		};

		Ok(keys)
	}

	/// Synonym of `getPairs` that uses paged queries to first get the keys, and then
	/// map them to values one by one.
	///
	/// This can work with public nodes. But, expect it to be darn slow.
	pub(crate) async fn rpc_get_pairs_paged(
		&self,
		prefix: StorageKey,
		at: B::Hash,
	) -> Result<Vec<KeyValue>, &'static str> {
		let now = std::time::Instant::now();
		let keys = self.rpc_get_keys_paged(prefix, at).await?;
		let client = self.as_online().transport.remote_client.clone().unwrap();
		let thread_chunk_size = (keys.len() / self.as_online().threads).max(1);

		log::info!(
			target: LOG_TARGET,
			"Querying a total of {} keys, took {}s to fetch keys, splitting among {} threads, {} keys per thread",
			keys.len(),
			now.elapsed().as_secs(),
			self.as_online().threads,
			thread_chunk_size,
		);

		let mut handles = Vec::new();
		let keys_chunked: Vec<Vec<StorageKey>> =
			keys.chunks(thread_chunk_size).map(|s| s.into()).collect::<Vec<_>>();
		for thread_keys in keys_chunked {
			let thread_client = client.clone();
			let handle = std::thread::spawn(move || {
				let rt = tokio::runtime::Runtime::new().unwrap();

				let mut thread_key_values = Vec::with_capacity(thread_keys.len());
				for chunk_keys in thread_keys.chunks(DEFAULT_VALUE_DOWNLOAD_BATCH) {
					let batch = chunk_keys
						.iter()
						.cloned()
						.map(|key| ("state_getStorage", rpc_params![key, at]))
						.collect::<Vec<_>>();

					let values =
						rt.block_on(thread_client.batch_request::<Option<StorageData>>(batch))
							.map_err(|e| {
								log::error!(
									target: LOG_TARGET,
									"failed to execute batch of {} values. Error: {:?}",
									chunk_keys.len(),
									e
								);
								"batch failed."
							})
							.unwrap();

					for (idx, key) in chunk_keys.iter().enumerate() {
						let maybe_value = values[idx].clone();
						let value = maybe_value.unwrap_or_else(|| {
							log::warn!(
								target: LOG_TARGET,
								"key {:?} had none corresponding value.",
								&key
							);
							StorageData(vec![])
						});
						thread_key_values.push((key.clone(), value));
						if thread_key_values.len() % (10 * DEFAULT_VALUE_DOWNLOAD_BATCH) == 0 {
							let ratio: f64 =
								thread_key_values.len() as f64 / thread_keys.len() as f64;
							log::debug!(
								target: LOG_TARGET,
								"[thread = {:?}] progress = {:.2} [{} / {}]",
								std::thread::current().id(),
								ratio,
								thread_key_values.len(),
								thread_keys.len(),
							);
						}
					}
				}
				thread_key_values
			});
			handles.push(handle);
		}

		let keys_and_values =
			handles.into_iter().map(|h| h.join().unwrap()).flatten().collect::<Vec<_>>();

		Ok(keys_and_values)
	}

	/// Get the values corresponding to `child_keys` at the given `prefixed_top_key`.
	pub(crate) async fn rpc_child_get_storage_paged(
		&self,
		prefixed_top_key: &StorageKey,
		child_keys: Vec<StorageKey>,
		at: B::Hash,
	) -> Result<Vec<KeyValue>, &'static str> {
		let mut child_kv_inner = vec![];
		for batch_child_key in child_keys.chunks(DEFAULT_VALUE_DOWNLOAD_BATCH) {
			let batch_request = batch_child_key
				.iter()
				.cloned()
				.map(|key| {
					(
						"childstate_getStorage",
						rpc_params![
							PrefixedStorageKey::new(prefixed_top_key.as_ref().to_vec()),
							key,
							at
						],
					)
				})
				.collect::<Vec<_>>();

			let batch_response = self
				.as_online()
				.rpc_client()
				.batch_request::<Option<StorageData>>(batch_request)
				.await
				.map_err(|e| {
					log::error!(
						target: LOG_TARGET,
						"failed to execute batch: {:?}. Error: {:?}",
						batch_child_key,
						e
					);
					"batch failed."
				})?;

			assert_eq!(batch_child_key.len(), batch_response.len());

			for (idx, key) in batch_child_key.iter().enumerate() {
				let maybe_value = batch_response[idx].clone();
				let value = maybe_value.unwrap_or_else(|| {
					log::warn!(target: LOG_TARGET, "key {:?} had none corresponding value.", &key);
					StorageData(vec![])
				});
				child_kv_inner.push((key.clone(), value));
			}
		}

		Ok(child_kv_inner)
	}

	pub(crate) async fn rpc_child_get_keys(
		&self,
		prefixed_top_key: &StorageKey,
		child_prefix: StorageKey,
		at: B::Hash,
	) -> Result<Vec<StorageKey>, &'static str> {
		let child_keys = self
			.as_online()
			.rpc_client()
			.child_get_keys(
				PrefixedStorageKey::new(prefixed_top_key.as_ref().to_vec()),
				child_prefix,
				Some(at),
			)
			.await
			.map_err(|e| {
				error!(target: LOG_TARGET, "Error = {:?}", e);
				"rpc child_get_keys failed."
			})?;

		debug!(
			target: LOG_TARGET,
			"scraped {} child-keys of the child-bearing top key: {}",
			child_keys.len(),
			HexDisplay::from(prefixed_top_key)
		);

		Ok(child_keys)
	}
}

// Internal methods
impl<B: BlockT + DeserializeOwned> Builder<B> {
	/// Load all of the child keys from the remote config, given the already scraped list of top key
	/// pairs.
	///
	/// `top_kv` need not be only child-bearing top keys. It should be all of the top keys that are
	/// included thus far.
	async fn load_child_remote(&self, top_kv: &[KeyValue]) -> Result<ChildKeyValues, &'static str> {
		let child_roots = top_kv
			.iter()
			.filter_map(|(k, _)| is_default_child_storage_key(k.as_ref()).then(|| k))
			.collect::<Vec<_>>();

		if child_roots.is_empty() {
			return Ok(Default::default())
		}

		info!(
			target: LOG_TARGET,
			"👩‍👦 scraping child-tree data from {} top keys",
			child_roots.len()
		);

		let mut child_kv = vec![];
		for prefixed_top_key in child_roots {
			let at = self.as_online().at_expected();
			let child_keys =
				self.rpc_child_get_keys(prefixed_top_key, StorageKey(vec![]), at).await?;
			let child_kv_inner =
				self.rpc_child_get_storage_paged(prefixed_top_key, child_keys, at).await?;

			let prefixed_top_key = PrefixedStorageKey::new(prefixed_top_key.clone().0);
			let un_prefixed = match ChildType::from_prefixed_key(&prefixed_top_key) {
				Some((ChildType::ParentKeyId, storage_key)) => storage_key,
				None => {
					log::error!(target: LOG_TARGET, "invalid key: {:?}", prefixed_top_key);
					return Err("Invalid child key")
				},
			};

			child_kv.push((ChildInfo::new_default(un_prefixed), child_kv_inner));
		}

		Ok(child_kv)
	}

	/// Build `Self` from a network node denoted by `uri`.
	async fn load_top_remote(&self) -> Result<TopKeyValues, &'static str> {
		let config = self.as_online();
		let at = self
			.as_online()
			.at
			.expect("online config must be initialized by this point; qed.");
		log::info!(target: LOG_TARGET, "scraping key-pairs from remote @{:?}", at);

		let mut keys_and_values = Vec::new();
		for prefix in &config.hashed_prefixes {
			let now = std::time::Instant::now();
			let additional_key_values =
				self.rpc_get_pairs_paged(StorageKey(prefix.to_vec()), at).await?;
			let elapsed = now.elapsed();
			log::info!(
				target: LOG_TARGET,
				"adding data for hashed prefix: {:?}, took {:?}s",
				HexDisplay::from(prefix),
				elapsed.as_secs()
			);
			keys_and_values.extend(additional_key_values);
		}

		for key in &config.hashed_keys {
			let key = StorageKey(key.to_vec());
			log::info!(
				target: LOG_TARGET,
				"adding data for hashed key: {:?}",
				HexDisplay::from(&key)
			);
			let value = self.rpc_get_storage(key.clone(), Some(at)).await?;
			keys_and_values.push((key, value));
		}

		Ok(keys_and_values)
	}

	pub(crate) async fn init_remote_client(&mut self) -> Result<(), &'static str> {
		// First, initialize the ws client.
		self.as_online_mut().transport.map_uri().await?;

		// Then, if `at` is not set, set it.
		if self.as_online().at.is_none() {
			let at = self.rpc_get_head().await?;
			log::info!(
				target: LOG_TARGET,
				"since no at is provided, setting it to latest finalized head, {:?}",
				at
			);
			self.as_online_mut().at = Some(at);
		}

		// Then, a few transformation that we want to perform in the online config:
		let online_config = self.as_online_mut();
		online_config
			.pallets
			.iter()
			.for_each(|p| online_config.hashed_prefixes.push(twox_128(p.as_bytes()).to_vec()));

		if online_config.child_trie {
			online_config.hashed_prefixes.push(DEFAULT_CHILD_STORAGE_KEY_PREFIX.to_vec());
		}

		// Finally, if by now, we have put any limitations on prefixes that we are interested in, we
		// download everything.
		if online_config
			.hashed_prefixes
			.iter()
			.filter(|p| *p != DEFAULT_CHILD_STORAGE_KEY_PREFIX)
			.count() == 0
		{
			log::info!(
				target: LOG_TARGET,
				"since no prefix is filtered, the data for all pallets will be downloaded"
			);
			online_config.hashed_prefixes.push(vec![]);
		}

		Ok(())
	}

	pub(crate) async fn load_remote_and_maybe_save(
		&mut self,
	) -> Result<(TopKeyValues, ChildKeyValues), &'static str> {
		let top_kv = self.load_top_remote().await?;
		let child_kv = self.load_child_remote(&top_kv).await?;

		if let Some(path) = self.as_online().state_snapshot.clone().map(|c| c.path) {
			let snapshot = Snapshot::<B> {
				top: top_kv.clone(),
				child: child_kv.clone(),
				block_hash: self
					.as_online()
					.at
					.expect("set to `Some` in `init_remote_client`; must be called before; qed"),
			};
			std::fs::write(path, snapshot.encode()).map_err(|_| "fs::write failed")?;
		}

		Ok((top_kv, child_kv))
	}

	pub(crate) fn load_snapshot(&mut self, path: PathBuf) -> Result<Snapshot<B>, &'static str> {
		info!(target: LOG_TARGET, "loading data from snapshot {:?}", path);
		let bytes = fs::read(path).map_err(|_| "fs::read failed.")?;
		Decode::decode(&mut &*bytes).map_err(|_| "decode failed")
	}

	async fn do_load_online(&mut self) -> Result<(TopKeyValues, ChildKeyValues), &'static str> {
		self.init_remote_client().await?;
		self.final_state_block_hash = Some(self.as_online().at_expected());
		Ok(self.load_remote_and_maybe_save().await?)
	}

	fn do_load_offline(
		&mut self,
		config: OfflineConfig,
	) -> Result<(TopKeyValues, ChildKeyValues), &'static str> {
		let Snapshot { block_hash, top, child } =
			self.load_snapshot(config.state_snapshot.path.clone())?;
		self.final_state_block_hash = Some(block_hash);
		Ok((top, child))
	}

	pub(crate) async fn pre_build(
		&mut self,
	) -> Result<(TopKeyValues, ChildKeyValues), &'static str> {
		let (mut top_kv, child_kv) = match self.mode.clone() {
			Mode::Offline(config) => self.do_load_offline(config)?,
			Mode::Online(_) => self.do_load_online().await?,
			Mode::OfflineOrElseOnline(offline_config, _) => {
				match self.do_load_offline(offline_config) {
					Ok(x) => x,
					Err(_) => self.do_load_online().await?,
				}
			},
		};

		// inject manual key values.
		if !self.hashed_key_values.is_empty() {
			log::info!(
				target: LOG_TARGET,
				"extending externalities with {} manually injected key-values",
				self.hashed_key_values.len()
			);
			top_kv.extend(self.hashed_key_values.clone());
		}

		// exclude manual key values.
		if !self.hashed_blacklist.is_empty() {
			log::info!(
				target: LOG_TARGET,
				"excluding externalities from {} keys",
				self.hashed_blacklist.len()
			);
			top_kv.retain(|(k, _)| !self.hashed_blacklist.contains(&k.0))
		}

		Ok((top_kv, child_kv))
	}
}

// Public methods
impl<B: BlockT + DeserializeOwned> Builder<B> {
	/// Create a new builder.
	pub fn new() -> Self {
		Default::default()
	}

	/// Inject a manual list of key and values to the storage.
	pub fn inject_hashed_key_value(mut self, injections: Vec<KeyValue>) -> Self {
		for i in injections {
			self.hashed_key_values.push(i.clone());
		}
		self
	}

	/// Blacklist this hashed key from the final externalities. This is treated as-is, and should be
	/// pre-hashed.
	pub fn blacklist_hashed_key(mut self, hashed: &[u8]) -> Self {
		self.hashed_blacklist.push(hashed.to_vec());
		self
	}

	/// Configure a state snapshot to be used.
	pub fn mode(mut self, mode: Mode<B>) -> Self {
		self.mode = mode;
		self
	}

	/// The state version to use.
	pub fn state_version(mut self, version: StateVersion) -> Self {
		self.state_version = version;
		self
	}

	/// Build the test externalities, and also return the final block hash to which the current
	/// state corresponds to.
	pub async fn build_with_block_hash(self) -> Result<(TestExternalities, B::Hash), &'static str> {
		self.do_build().await
	}

	pub async fn build(self) -> Result<TestExternalities, &'static str> {
		self.do_build().await.map(|(e, _)| e)
	}

	/// Build the test externalities.
	async fn do_build(mut self) -> Result<(TestExternalities, B::Hash), &'static str> {
		let state_version = self.state_version;
		let (top_kv, child_kv) = self.pre_build().await?;
		let mut ext = TestExternalities::new_with_code_and_state(
			Default::default(),
			Default::default(),
			state_version,
		);

		info!(target: LOG_TARGET, "injecting a total of {} top keys", top_kv.len());
		for (k, v) in top_kv {
			// skip writing the child root data.
			if is_default_child_storage_key(k.as_ref()) {
				continue
			}
			ext.insert(k.0, v.0);
		}

		info!(
			target: LOG_TARGET,
			"injecting a total of {} child keys",
			child_kv.iter().flat_map(|(_, kv)| kv).count()
		);

		for (info, key_values) in child_kv {
			for (k, v) in key_values {
				ext.insert_child(info.clone(), k.0, v.0);
			}
		}

		ext.commit_all().unwrap();
		info!(
			target: LOG_TARGET,
			"initialized state externalities with storage root {:?}",
			ext.as_backend().root()
		);

		Ok((ext, self.final_state_block_hash.unwrap()))
	}
}

#[cfg(test)]
mod test_prelude {
	use tracing_subscriber::EnvFilter;

	pub(crate) use super::*;
	pub(crate) use sp_runtime::testing::{Block as RawBlock, ExtrinsicWrapper, H256 as Hash};
	pub(crate) type Block = RawBlock<ExtrinsicWrapper<Hash>>;

	pub(crate) fn init_logger() {
		let _ = tracing_subscriber::fmt().with_env_filter(EnvFilter::from_default_env())
			.with_level(true)
			.try_init();
	}
}

#[cfg(test)]
mod tests {
	use super::test_prelude::*;

	#[tokio::test]
	async fn can_load_state_snapshot() {
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::OfflineOrElseOnline(
				OfflineConfig { state_snapshot: SnapshotConfig::new("test_data/proxy_test") },
				OnlineConfig {
					pallets: vec!["Proxy".to_owned()],
					child_trie: false,
					state_snapshot: Some(SnapshotConfig::new("test_data/proxy_test")),
					..Default::default()
				},
			))
			.build()
			.await
			.unwrap()
			.execute_with(|| {});
	}

	#[tokio::test]
	async fn can_exclude_from_snapshot() {
		init_logger();

		// get the first key from the snapshot file.
		let some_key = Builder::<Block>::new()
			.mode(Mode::Offline(OfflineConfig {
				state_snapshot: SnapshotConfig::new("test_data/proxy_test"),
			}))
			.build()
			.await
			.expect("Can't read state snapshot file")
			.execute_with(|| {
				let key =
					sp_io::storage::next_key(&[]).expect("some key must exist in the snapshot");
				assert!(sp_io::storage::get(&key).is_some());
				key
			});

		Builder::<Block>::new()
			.mode(Mode::Offline(OfflineConfig {
				state_snapshot: SnapshotConfig::new("test_data/proxy_test"),
			}))
			.blacklist_hashed_key(&some_key)
			.build()
			.await
			.expect("Can't read state snapshot file")
			.execute_with(|| assert!(sp_io::storage::get(&some_key).is_none()));
	}
}

#[cfg(all(test, feature = "remote-test"))]
mod remote_tests {
	use super::test_prelude::*;
	use std::os::unix::fs::MetadataExt;

	#[tokio::test]
	async fn single_thread_works() {
		todo!();
	}

	#[tokio::test]
	async fn single_multi_thread_result_is_same() {
		todo!();
	}

	#[tokio::test]
	async fn snapshot_block_hash_works() {
		const CACHE: &'static str = "snapshot_block_hash_works";
		init_logger();

		// first, build a snapshot.
		let (_, block_hash) = Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				pallets: vec!["Proxy".to_owned()],
				child_trie: false,
				state_snapshot: Some(SnapshotConfig::new(CACHE)),
				..Default::default()
			}))
			.build_with_block_hash()
			.await
			.unwrap();

		// now re-create the same snapshot.
		let (_, cached_block_hash) = Builder::<Block>::new()
			.mode(Mode::Offline(OfflineConfig { state_snapshot: SnapshotConfig::new(CACHE) }))
			.build_with_block_hash()
			.await
			.unwrap();

		assert_eq!(block_hash, cached_block_hash);
	}

	#[tokio::test]
	async fn offline_else_online_works() {
		const CACHE: &'static str = "offline_else_online_works_data";
		init_logger();
		// this shows that in the second run, we use the remote and create a snapshot.
		Builder::<Block>::new()
			.mode(Mode::OfflineOrElseOnline(
				OfflineConfig { state_snapshot: SnapshotConfig::new(CACHE) },
				OnlineConfig {
					pallets: vec!["Proxy".to_owned()],
					child_trie: false,
					state_snapshot: Some(SnapshotConfig::new(CACHE)),
					..Default::default()
				},
			))
			.build()
			.await
			.unwrap()
			.execute_with(|| {});

		// this shows that in the second run, we are not using the remote
		Builder::<Block>::new()
			.mode(Mode::OfflineOrElseOnline(
				OfflineConfig { state_snapshot: SnapshotConfig::new(CACHE) },
				OnlineConfig {
					transport: "ws://non-existent:666".to_owned().into(),
					..Default::default()
				},
			))
			.build()
			.await
			.unwrap()
			.execute_with(|| {});

		let to_delete = std::fs::read_dir(Path::new("."))
			.unwrap()
			.into_iter()
			.map(|d| d.unwrap())
			.filter(|p| p.path().file_name().unwrap_or_default() == CACHE)
			.collect::<Vec<_>>();

		assert!(to_delete.len() == 1);
		std::fs::remove_file(to_delete[0].path()).unwrap();
	}

	#[tokio::test]
	async fn can_build_one_small_pallet() {
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				pallets: vec!["Proxy".to_owned()],
				child_trie: false,
				..Default::default()
			}))
			.build()
			.await
			.unwrap()
			.execute_with(|| {});
	}

	#[tokio::test]
	async fn can_build_few_pallet() {
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				pallets: vec!["Proxy".to_owned(), "Multisig".to_owned()],
				child_trie: false,
				..Default::default()
			}))
			.build()
			.await
			.unwrap()
			.execute_with(|| {});
	}

	#[tokio::test(flavor = "multi_thread")]
	async fn can_build_big_pallet() {
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				transport: "wss://rpc.polkadot.io:443".into(),
				// transport: "wss://polkadot.api.onfinality.io:443/public-ws".into(),
				// transport: "wss://public-rpc.pinknode.io:443/polkadot".into(),
				// transport: "ws://127.0.0.1:9944".into(),
				pallets: vec!["Staking".to_owned()],
				child_trie: false,
				threads:2 ,
				..Default::default()
			}))
			.build()
			.await
			.unwrap()
			.execute_with(|| {});
	}

	#[tokio::test]
	async fn can_create_snapshot() {
		const CACHE: &'static str = "can_create_snapshot";
		init_logger();

		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				state_snapshot: Some(SnapshotConfig::new(CACHE)),
				pallets: vec!["Proxy".to_owned()],
				child_trie: false,
				..Default::default()
			}))
			.build()
			.await
			.unwrap()
			.execute_with(|| {});

		let to_delete = std::fs::read_dir(Path::new("."))
			.unwrap()
			.into_iter()
			.map(|d| d.unwrap())
			.filter(|p| p.path().file_name().unwrap_or_default() == CACHE)
			.collect::<Vec<_>>();

		let snap: Snapshot<Block> = Builder::<Block>::new().load_snapshot(CACHE.into()).unwrap();
		assert!(matches!(snap, Snapshot { top, child, .. } if top.len() > 0 && child.len() == 0));

		assert!(to_delete.len() == 1);
		let to_delete = to_delete.first().unwrap();
		assert!(std::fs::metadata(to_delete.path()).unwrap().size() > 1);
		std::fs::remove_file(to_delete.path()).unwrap();
	}

	#[tokio::test]
	async fn can_create_child_snapshot() {
		const CACHE: &'static str = "can_create_child_snapshot";
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				state_snapshot: Some(SnapshotConfig::new(CACHE)),
				pallets: vec!["Crowdloan".to_owned()],
				child_trie: true,
				..Default::default()
			}))
			.build()
			.await
			.unwrap()
			.execute_with(|| {});

		let to_delete = std::fs::read_dir(Path::new("."))
			.unwrap()
			.into_iter()
			.map(|d| d.unwrap())
			.filter(|p| p.path().file_name().unwrap_or_default() == CACHE)
			.collect::<Vec<_>>();

		let snap: Snapshot<Block> = Builder::<Block>::new().load_snapshot(CACHE.into()).unwrap();
		assert!(matches!(snap, Snapshot { top, child, .. } if top.len() > 0 && child.len() > 0));

		assert!(to_delete.len() == 1);
		let to_delete = to_delete.first().unwrap();
		assert!(std::fs::metadata(to_delete.path()).unwrap().size() > 1);
		std::fs::remove_file(to_delete.path()).unwrap();
	}

	#[tokio::test]
	// #[ignore = "only works if a local node is present."]
	async fn can_fetch_all_local() {
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				transport: "ws://localhost:9944".into(),
				..Default::default()
			}))
			.build()
			.await
			.unwrap()
			.execute_with(|| {});
	}

	#[tokio::test]
	// #[ignore = "slow af."]
	async fn can_fetch_all_remote() {
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig::default()))
			.build()
			.await
			.unwrap()
			.execute_with(|| {});
	}
}
