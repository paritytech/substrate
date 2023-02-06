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
use futures::{channel::mpsc, stream::StreamExt};
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
use sp_runtime::{traits::Block as BlockT, StateVersion};
use std::{
	fs,
	num::NonZeroUsize,
	ops::{Deref, DerefMut},
	path::{Path, PathBuf},
	sync::Arc,
	thread,
};
use substrate_rpc_client::{
	rpc_params, ws_client, BatchRequestBuilder, ChainApi, ClientT, StateApi, WsClient,
};

type KeyValue = (StorageKey, StorageData);
type TopKeyValues = Vec<KeyValue>;
type ChildKeyValues = Vec<(ChildInfo, Vec<KeyValue>)>;

const LOG_TARGET: &str = "remote-ext";
const DEFAULT_WS_ENDPOINT: &str = "wss://rpc.polkadot.io:443";
const DEFAULT_VALUE_DOWNLOAD_BATCH: usize = 4096;
// NOTE: increasing this value does not seem to impact speed all that much.
const DEFAULT_KEY_DOWNLOAD_PAGE: u32 = 1000;
/// The snapshot that we store on disk.
#[derive(Decode, Encode)]
struct Snapshot<B: BlockT> {
	state_version: StateVersion,
	block_hash: B::Hash,
	top: TopKeyValues,
	child: ChildKeyValues,
}

/// An externalities that acts exactly the same as [`sp_io::TestExternalities`] but has a few extra
/// bits and pieces to it, and can be loaded remotely.
pub struct RemoteExternalities<B: BlockT> {
	/// The inner externalities.
	pub inner_ext: TestExternalities,
	/// The block hash it which we created this externality env.
	pub block_hash: B::Hash,
}

impl<B: BlockT> Deref for RemoteExternalities<B> {
	type Target = TestExternalities;
	fn deref(&self) -> &Self::Target {
		&self.inner_ext
	}
}

impl<B: BlockT> DerefMut for RemoteExternalities<B> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.inner_ext
	}
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
pub enum Transport {
	/// Use the `URI` to open a new WebSocket connection.
	Uri(String),
	/// Use existing WebSocket connection.
	RemoteClient(Arc<WsClient>),
}

impl Transport {
	fn as_client(&self) -> Option<&WsClient> {
		match self {
			Self::RemoteClient(client) => Some(client),
			_ => None,
		}
	}

	fn as_client_cloned(&self) -> Option<Arc<WsClient>> {
		match self {
			Self::RemoteClient(client) => Some(client.clone()),
			_ => None,
		}
	}

	// Open a new WebSocket connection if it's not connected.
	async fn map_uri(&mut self) -> Result<(), &'static str> {
		if let Self::Uri(uri) = self {
			log::debug!(target: LOG_TARGET, "initializing remote client to {:?}", uri);

			let ws_client = ws_client(uri).await.map_err(|e| {
				log::error!(target: LOG_TARGET, "error: {:?}", e);
				"failed to build ws client"
			})?;

			*self = Self::RemoteClient(Arc::new(ws_client))
		}

		Ok(())
	}
}

impl From<String> for Transport {
	fn from(uri: String) -> Self {
		Transport::Uri(uri)
	}
}

impl From<Arc<WsClient>> for Transport {
	fn from(client: Arc<WsClient>) -> Self {
		Transport::RemoteClient(client)
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
}

impl<B: BlockT> OnlineConfig<B> {
	/// Return rpc (ws) client reference.
	fn rpc_client(&self) -> &WsClient {
		self.transport
			.as_client()
			.expect("ws client must have been initialized by now; qed.")
	}

	/// Return a cloned rpc (ws) client, suitable for being moved to threads.
	fn rpc_client_cloned(&self) -> Arc<WsClient> {
		self.transport
			.as_client_cloned()
			.expect("ws client must have been initialized by now; qed.")
	}

	fn at_expected(&self) -> B::Hash {
		self.at.expect("block at must be initialized; qed")
	}
}

impl<B: BlockT> Default for OnlineConfig<B> {
	fn default() -> Self {
		Self {
			transport: Transport::from(DEFAULT_WS_ENDPOINT.to_owned()),
			child_trie: true,
			at: None,
			state_snapshot: None,
			pallets: Default::default(),
			hashed_keys: Default::default(),
			hashed_prefixes: Default::default(),
		}
	}
}

impl<B: BlockT> From<String> for OnlineConfig<B> {
	fn from(t: String) -> Self {
		Self { transport: t.into(), ..Default::default() }
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
	/// Connectivity mode, online or offline.
	mode: Mode<B>,
	/// If provided, overwrite the state version with this. Otherwise, the state_version of the
	/// remote node is used. All cache files also store their state version.
	///
	/// Overwrite only with care.
	overwrite_state_version: Option<StateVersion>,
}

// NOTE: ideally we would use `DefaultNoBound` here, but not worth bringing in frame-support for
// that.
impl<B: BlockT> Default for Builder<B> {
	fn default() -> Self {
		Self {
			mode: Default::default(),
			hashed_key_values: Default::default(),
			hashed_blacklist: Default::default(),
			overwrite_state_version: None,
		}
	}
}

// Mode methods
impl<B: BlockT> Builder<B> {
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
impl<B: BlockT> Builder<B>
where
	B::Hash: DeserializeOwned,
	B::Header: DeserializeOwned,
{
	/// Get the number of threads to use.
	fn threads() -> NonZeroUsize {
		thread::available_parallelism()
			.unwrap_or(NonZeroUsize::new(4usize).expect("4 is non-zero; qed"))
	}

	async fn rpc_get_storage(
		&self,
		key: StorageKey,
		maybe_at: Option<B::Hash>,
	) -> Result<Option<StorageData>, &'static str> {
		trace!(target: LOG_TARGET, "rpc: get_storage");
		self.as_online().rpc_client().storage(key, maybe_at).await.map_err(|e| {
			error!(target: LOG_TARGET, "Error = {:?}", e);
			"rpc get_storage failed."
		})
	}

	/// Get the latest finalized head.
	async fn rpc_get_head(&self) -> Result<B::Hash, &'static str> {
		trace!(target: LOG_TARGET, "rpc: finalized_head");

		// sadly this pretty much unreadable...
		ChainApi::<(), _, B::Header, ()>::finalized_head(self.as_online().rpc_client())
			.await
			.map_err(|e| {
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
				.storage_keys_paged(
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
		pending_ext: &mut TestExternalities,
	) -> Result<Vec<KeyValue>, &'static str> {
		let keys = self.rpc_get_keys_paged(prefix.clone(), at).await?;
		if keys.is_empty() {
			return Ok(Default::default())
		}

		let client = self.as_online().rpc_client_cloned();
		let threads = Self::threads().get();
		let thread_chunk_size = (keys.len() + threads - 1) / threads;

		log::info!(
			target: LOG_TARGET,
			"Querying a total of {} keys from prefix {:?}, splitting among {} threads, {} keys per thread",
			keys.len(),
			HexDisplay::from(&prefix),
			threads,
			thread_chunk_size,
		);

		let mut handles = Vec::new();
		let keys_chunked: Vec<Vec<StorageKey>> =
			keys.chunks(thread_chunk_size).map(|s| s.into()).collect::<Vec<_>>();

		enum Message {
			/// This thread completed the assigned work.
			Terminated,
			/// The thread produced the following batch response.
			Batch(Vec<(Vec<u8>, Vec<u8>)>),
			/// A request from the batch failed.
			BatchFailed(String),
		}

		let (tx, mut rx) = mpsc::unbounded::<Message>();

		for thread_keys in keys_chunked {
			let thread_client = client.clone();
			let thread_sender = tx.clone();
			let handle = std::thread::spawn(move || {
				let rt = tokio::runtime::Runtime::new().unwrap();
				let mut thread_key_values = Vec::with_capacity(thread_keys.len());

				for chunk_keys in thread_keys.chunks(DEFAULT_VALUE_DOWNLOAD_BATCH) {
					let mut batch = BatchRequestBuilder::new();

					for key in chunk_keys.iter() {
						batch
							.insert("state_getStorage", rpc_params![key, at])
							.map_err(|_| "Invalid batch params")
							.unwrap();
					}

					let batch_response = rt
						.block_on(thread_client.batch_request::<Option<StorageData>>(batch))
						.map_err(|e| {
							log::error!(
								target: LOG_TARGET,
								"failed to execute batch: {:?}. Error: {:?}",
								chunk_keys.iter().map(HexDisplay::from).collect::<Vec<_>>(),
								e
							);
							"batch failed."
						})
						.unwrap();

					// Check if we got responses for all submitted requests.
					assert_eq!(chunk_keys.len(), batch_response.len());

					let mut batch_kv = Vec::with_capacity(chunk_keys.len());
					for (key, maybe_value) in chunk_keys.into_iter().zip(batch_response) {
						match maybe_value {
							Ok(Some(data)) => {
								thread_key_values.push((key.clone(), data.clone()));
								batch_kv.push((key.clone().0, data.0));
							},
							Ok(None) => {
								log::warn!(
									target: LOG_TARGET,
									"key {:?} had none corresponding value.",
									&key
								);
								let data = StorageData(vec![]);
								thread_key_values.push((key.clone(), data.clone()));
								batch_kv.push((key.clone().0, data.0));
							},
							Err(e) => {
								let reason = format!("key {:?} failed: {:?}", &key, e);
								log::error!(target: LOG_TARGET, "Reason: {}", reason);
								// Signal failures to the main thread, stop aggregating (key, value)
								// pairs and return immediately an error.
								thread_sender.unbounded_send(Message::BatchFailed(reason)).unwrap();
								return Default::default()
							},
						};

						if thread_key_values.len() % (thread_keys.len() / 10).max(1) == 0 {
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

					// Send this batch to the main thread to start inserting.
					thread_sender.unbounded_send(Message::Batch(batch_kv)).unwrap();
				}

				thread_sender.unbounded_send(Message::Terminated).unwrap();
				thread_key_values
			});

			handles.push(handle);
		}

		// first, wait until all threads send a `Terminated` message, in the meantime populate
		// `pending_ext`.
		let mut terminated = 0usize;
		let mut batch_failed = false;
		loop {
			match rx.next().await.unwrap() {
				Message::Batch(kv) => {
					for (k, v) in kv {
						// skip writing the child root data.
						if is_default_child_storage_key(k.as_ref()) {
							continue
						}
						pending_ext.insert(k, v);
					}
				},
				Message::BatchFailed(error) => {
					log::error!(target: LOG_TARGET, "Batch processing failed: {:?}", error);
					batch_failed = true;
					break
				},
				Message::Terminated => {
					terminated += 1;
					if terminated == handles.len() {
						break
					}
				},
			}
		}

		// Ensure all threads finished execution before returning.
		let keys_and_values =
			handles.into_iter().flat_map(|h| h.join().unwrap()).collect::<Vec<_>>();

		if batch_failed {
			return Err("Batch failed.")
		}

		Ok(keys_and_values)
	}

	/// Get the values corresponding to `child_keys` at the given `prefixed_top_key`.
	pub(crate) async fn rpc_child_get_storage_paged(
		client: &WsClient,
		prefixed_top_key: &StorageKey,
		child_keys: Vec<StorageKey>,
		at: B::Hash,
	) -> Result<Vec<KeyValue>, &'static str> {
		let mut child_kv_inner = vec![];
		let mut batch_success = true;

		for batch_child_key in child_keys.chunks(DEFAULT_VALUE_DOWNLOAD_BATCH) {
			let mut batch_request = BatchRequestBuilder::new();

			for key in batch_child_key {
				batch_request
					.insert(
						"childstate_getStorage",
						rpc_params![
							PrefixedStorageKey::new(prefixed_top_key.as_ref().to_vec()),
							key,
							at
						],
					)
					.map_err(|_| "Invalid batch params")?;
			}

			let batch_response =
				client.batch_request::<Option<StorageData>>(batch_request).await.map_err(|e| {
					log::error!(
						target: LOG_TARGET,
						"failed to execute batch: {:?}. Error: {:?}",
						batch_child_key,
						e
					);
					"batch failed."
				})?;

			assert_eq!(batch_child_key.len(), batch_response.len());

			for (key, maybe_value) in batch_child_key.iter().zip(batch_response) {
				match maybe_value {
					Ok(Some(v)) => {
						child_kv_inner.push((key.clone(), v));
					},
					Ok(None) => {
						log::warn!(
							target: LOG_TARGET,
							"key {:?} had none corresponding value.",
							&key
						);
						child_kv_inner.push((key.clone(), StorageData(vec![])));
					},
					Err(e) => {
						log::error!(target: LOG_TARGET, "key {:?} failed: {:?}", &key, e);
						batch_success = false;
					},
				};
			}
		}

		if batch_success {
			Ok(child_kv_inner)
		} else {
			Err("batch failed.")
		}
	}

	pub(crate) async fn rpc_child_get_keys(
		client: &WsClient,
		prefixed_top_key: &StorageKey,
		child_prefix: StorageKey,
		at: B::Hash,
	) -> Result<Vec<StorageKey>, &'static str> {
		// This is deprecated and will generate a warning which causes the CI to fail.
		#[allow(warnings)]
		let child_keys = substrate_rpc_client::ChildStateApi::storage_keys(
			client,
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
			"[thread = {:?}] scraped {} child-keys of the child-bearing top key: {}",
			std::thread::current().id(),
			child_keys.len(),
			HexDisplay::from(prefixed_top_key)
		);

		Ok(child_keys)
	}
}

impl<B: BlockT + DeserializeOwned> Builder<B>
where
	B::Hash: DeserializeOwned,
	B::Header: DeserializeOwned,
{
	/// Load all of the child keys from the remote config, given the already scraped list of top key
	/// pairs.
	///
	/// `top_kv` need not be only child-bearing top keys. It should be all of the top keys that are
	/// included thus far.
	///
	/// This function concurrently populates `pending_ext`. the return value is only for writing to
	/// cache, we can also optimize further.
	async fn load_child_remote(
		&self,
		top_kv: &[KeyValue],
		pending_ext: &mut TestExternalities,
	) -> Result<ChildKeyValues, &'static str> {
		let child_roots = top_kv
			.into_iter()
			.filter_map(|(k, _)| is_default_child_storage_key(k.as_ref()).then(|| k.clone()))
			.collect::<Vec<_>>();

		if child_roots.is_empty() {
			return Ok(Default::default())
		}

		// div-ceil simulation.
		let threads = Self::threads().get();
		let child_roots_per_thread = (child_roots.len() + threads - 1) / threads;

		info!(
			target: LOG_TARGET,
			"👩‍👦 scraping child-tree data from {} top keys, split among {} threads, {} top keys per thread",
			child_roots.len(),
			threads,
			child_roots_per_thread,
		);

		// NOTE: the threading done here is the simpler, yet slightly un-elegant because we are
		// splitting child root among threads, and it is very common for these root to have vastly
		// different child tries underneath them, causing some threads to finish way faster than
		// others. Certainly still better than single thread though.
		let mut handles = vec![];
		let client = self.as_online().rpc_client_cloned();
		let at = self.as_online().at_expected();

		enum Message {
			Terminated,
			Batch((ChildInfo, Vec<(Vec<u8>, Vec<u8>)>)),
		}
		let (tx, mut rx) = mpsc::unbounded::<Message>();

		for thread_child_roots in child_roots
			.chunks(child_roots_per_thread)
			.map(|x| x.into())
			.collect::<Vec<Vec<_>>>()
		{
			let thread_client = client.clone();
			let thread_sender = tx.clone();
			let handle = thread::spawn(move || {
				let rt = tokio::runtime::Runtime::new().unwrap();
				let mut thread_child_kv = vec![];
				for prefixed_top_key in thread_child_roots {
					let child_keys = rt.block_on(Self::rpc_child_get_keys(
						&thread_client,
						&prefixed_top_key,
						StorageKey(vec![]),
						at,
					))?;
					let child_kv_inner = rt.block_on(Self::rpc_child_get_storage_paged(
						&thread_client,
						&prefixed_top_key,
						child_keys,
						at,
					))?;

					let prefixed_top_key = PrefixedStorageKey::new(prefixed_top_key.clone().0);
					let un_prefixed = match ChildType::from_prefixed_key(&prefixed_top_key) {
						Some((ChildType::ParentKeyId, storage_key)) => storage_key,
						None => {
							log::error!(target: LOG_TARGET, "invalid key: {:?}", prefixed_top_key);
							return Err("Invalid child key")
						},
					};

					thread_sender
						.unbounded_send(Message::Batch((
							ChildInfo::new_default(un_prefixed),
							child_kv_inner
								.iter()
								.cloned()
								.map(|(k, v)| (k.0, v.0))
								.collect::<Vec<_>>(),
						)))
						.unwrap();
					thread_child_kv.push((ChildInfo::new_default(un_prefixed), child_kv_inner));
				}

				thread_sender.unbounded_send(Message::Terminated).unwrap();
				Ok(thread_child_kv)
			});
			handles.push(handle);
		}

		// first, wait until all threads send a `Terminated` message, in the meantime populate
		// `pending_ext`.
		let mut terminated = 0usize;
		loop {
			match rx.next().await.unwrap() {
				Message::Batch((info, kvs)) =>
					for (k, v) in kvs {
						pending_ext.insert_child(info.clone(), k, v);
					},
				Message::Terminated => {
					terminated += 1;
					if terminated == handles.len() {
						break
					}
				},
			}
		}

		let child_kv = handles
			.into_iter()
			.flat_map(|h| h.join().unwrap())
			.flatten()
			.collect::<Vec<_>>();
		Ok(child_kv)
	}

	/// Build `Self` from a network node denoted by `uri`.
	///
	/// This function concurrently populates `pending_ext`. the return value is only for writing to
	/// cache, we can also optimize further.
	async fn load_top_remote(
		&self,
		pending_ext: &mut TestExternalities,
	) -> Result<TopKeyValues, &'static str> {
		let config = self.as_online();
		let at = self
			.as_online()
			.at
			.expect("online config must be initialized by this point; qed.");
		log::info!(target: LOG_TARGET, "scraping key-pairs from remote at block height {:?}", at);

		let mut keys_and_values = Vec::new();
		for prefix in &config.hashed_prefixes {
			let now = std::time::Instant::now();
			let additional_key_values =
				self.rpc_get_pairs_paged(StorageKey(prefix.to_vec()), at, pending_ext).await?;
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
			match self.rpc_get_storage(key.clone(), Some(at)).await? {
				Some(value) => {
					pending_ext.insert(key.clone().0, value.clone().0);
					keys_and_values.push((key, value));
				},
				None => {
					log::warn!(
						target: LOG_TARGET,
						"no data found for hashed key: {:?}",
						HexDisplay::from(&key)
					);
				},
			}
		}

		Ok(keys_and_values)
	}

	/// The entry point of execution, if `mode` is online.
	///
	/// initializes the remote client in `transport`, and sets the `at` field, if not specified.
	async fn init_remote_client(&mut self) -> Result<(), &'static str> {
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

	/// Load the data from a remote server. The main code path is calling into `load_top_remote` and
	/// `load_child_remote`.
	///
	/// Must be called after `init_remote_client`.
	async fn load_remote_and_maybe_save(&mut self) -> Result<TestExternalities, &'static str> {
		let state_version =
			StateApi::<B::Hash>::runtime_version(self.as_online().rpc_client(), None)
				.await
				.map_err(|e| {
					error!(target: LOG_TARGET, "Error = {:?}", e);
					"rpc runtime_version failed."
				})
				.map(|v| v.state_version())?;
		let mut pending_ext = TestExternalities::new_with_code_and_state(
			Default::default(),
			Default::default(),
			self.overwrite_state_version.unwrap_or(state_version),
		);
		let top_kv = self.load_top_remote(&mut pending_ext).await?;
		let child_kv = self.load_child_remote(&top_kv, &mut pending_ext).await?;

		if let Some(path) = self.as_online().state_snapshot.clone().map(|c| c.path) {
			let snapshot = Snapshot::<B> {
				state_version,
				top: top_kv,
				child: child_kv,
				block_hash: self
					.as_online()
					.at
					.expect("set to `Some` in `init_remote_client`; must be called before; qed"),
			};
			let encoded = snapshot.encode();
			log::info!(
				target: LOG_TARGET,
				"writing snapshot of {} bytes to {:?}",
				encoded.len(),
				path
			);
			std::fs::write(path, encoded).map_err(|_| "fs::write failed")?;
		}

		Ok(pending_ext)
	}

	fn load_snapshot(&mut self, path: PathBuf) -> Result<Snapshot<B>, &'static str> {
		info!(target: LOG_TARGET, "loading data from snapshot {:?}", path);
		let bytes = fs::read(path).map_err(|_| "fs::read failed.")?;
		Decode::decode(&mut &*bytes).map_err(|_| "decode failed")
	}

	async fn do_load_remote(&mut self) -> Result<RemoteExternalities<B>, &'static str> {
		self.init_remote_client().await?;
		let block_hash = self.as_online().at_expected();
		let inner_ext = self.load_remote_and_maybe_save().await?;
		Ok(RemoteExternalities { block_hash, inner_ext })
	}

	fn do_load_offline(
		&mut self,
		config: OfflineConfig,
	) -> Result<RemoteExternalities<B>, &'static str> {
		let Snapshot { block_hash, top, child, state_version } =
			self.load_snapshot(config.state_snapshot.path.clone())?;

		let mut inner_ext = TestExternalities::new_with_code_and_state(
			Default::default(),
			Default::default(),
			self.overwrite_state_version.unwrap_or(state_version),
		);

		info!(target: LOG_TARGET, "injecting a total of {} top keys", top.len());
		for (k, v) in top {
			// skip writing the child root data.
			if is_default_child_storage_key(k.as_ref()) {
				continue
			}
			inner_ext.insert(k.0, v.0);
		}

		info!(
			target: LOG_TARGET,
			"injecting a total of {} child keys",
			child.iter().flat_map(|(_, kv)| kv).count()
		);

		for (info, key_values) in child {
			for (k, v) in key_values {
				inner_ext.insert_child(info.clone(), k.0, v.0);
			}
		}

		Ok(RemoteExternalities { inner_ext, block_hash })
	}

	pub(crate) async fn pre_build(mut self) -> Result<RemoteExternalities<B>, &'static str> {
		let mut ext = match self.mode.clone() {
			Mode::Offline(config) => self.do_load_offline(config)?,
			Mode::Online(_) => self.do_load_remote().await?,
			Mode::OfflineOrElseOnline(offline_config, _) => {
				match self.do_load_offline(offline_config) {
					Ok(x) => x,
					Err(_) => self.do_load_remote().await?,
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
			for (k, v) in self.hashed_key_values {
				ext.insert(k.0, v.0);
			}
		}

		// exclude manual key values.
		if !self.hashed_blacklist.is_empty() {
			log::info!(
				target: LOG_TARGET,
				"excluding externalities from {} keys",
				self.hashed_blacklist.len()
			);
			for k in self.hashed_blacklist {
				ext.execute_with(|| sp_io::storage::clear(&k));
			}
		}

		Ok(ext)
	}
}

// Public methods
impl<B: BlockT + DeserializeOwned> Builder<B>
where
	B::Hash: DeserializeOwned,
	B::Header: DeserializeOwned,
{
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
	pub fn overwrite_state_version(mut self, version: StateVersion) -> Self {
		self.overwrite_state_version = Some(version);
		self
	}

	pub async fn build(self) -> Result<RemoteExternalities<B>, &'static str> {
		let mut ext = self.pre_build().await?;
		ext.commit_all().unwrap();

		info!(
			target: LOG_TARGET,
			"initialized state externalities with storage root {:?} and state_version {:?}",
			ext.as_backend().root(),
			ext.state_version
		);

		Ok(ext)
	}
}

#[cfg(test)]
mod test_prelude {
	use tracing_subscriber::EnvFilter;

	pub(crate) use super::*;
	pub(crate) use sp_runtime::testing::{Block as RawBlock, ExtrinsicWrapper, H256 as Hash};
	pub(crate) type Block = RawBlock<ExtrinsicWrapper<Hash>>;

	pub(crate) fn init_logger() {
		let _ = tracing_subscriber::fmt()
			.with_env_filter(EnvFilter::from_default_env())
			.with_level(true)
			.try_init();
	}
}

#[cfg(test)]
mod tests {
	use super::test_prelude::*;

	#[tokio::test(flavor = "multi_thread")]
	async fn can_load_state_snapshot() {
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::Offline(OfflineConfig {
				state_snapshot: SnapshotConfig::new("test_data/proxy_test"),
			}))
			.build()
			.await
			.unwrap()
			.execute_with(|| {});
	}

	#[tokio::test(flavor = "multi_thread")]
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

	#[tokio::test(flavor = "multi_thread")]
	async fn state_version_is_kept_and_can_be_altered() {
		const CACHE: &'static str = "state_version_is_kept_and_can_be_altered";
		init_logger();

		// first, build a snapshot.
		let ext = Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				pallets: vec!["Proxy".to_owned()],
				child_trie: false,
				state_snapshot: Some(SnapshotConfig::new(CACHE)),
				..Default::default()
			}))
			.build()
			.await
			.unwrap();

		// now re-create the same snapshot.
		let cached_ext = Builder::<Block>::new()
			.mode(Mode::Offline(OfflineConfig { state_snapshot: SnapshotConfig::new(CACHE) }))
			.build()
			.await
			.unwrap();

		assert_eq!(ext.state_version, cached_ext.state_version);

		// now overwrite it
		let other = match ext.state_version {
			StateVersion::V0 => StateVersion::V1,
			StateVersion::V1 => StateVersion::V0,
		};
		let cached_ext = Builder::<Block>::new()
			.mode(Mode::Offline(OfflineConfig { state_snapshot: SnapshotConfig::new(CACHE) }))
			.overwrite_state_version(other)
			.build()
			.await
			.unwrap();

		assert_eq!(cached_ext.state_version, other);
	}

	#[tokio::test(flavor = "multi_thread")]
	async fn snapshot_block_hash_works() {
		const CACHE: &'static str = "snapshot_block_hash_works";
		init_logger();

		// first, build a snapshot.
		let ext = Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				pallets: vec!["Proxy".to_owned()],
				child_trie: false,
				state_snapshot: Some(SnapshotConfig::new(CACHE)),
				..Default::default()
			}))
			.build()
			.await
			.unwrap();

		// now re-create the same snapshot.
		let cached_ext = Builder::<Block>::new()
			.mode(Mode::Offline(OfflineConfig { state_snapshot: SnapshotConfig::new(CACHE) }))
			.build()
			.await
			.unwrap();

		assert_eq!(ext.block_hash, cached_ext.block_hash);
	}

	#[tokio::test(flavor = "multi_thread")]
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

	#[tokio::test(flavor = "multi_thread")]
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

	#[tokio::test(flavor = "multi_thread")]
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

	#[tokio::test(flavor = "multi_thread")]
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

	#[tokio::test(flavor = "multi_thread")]
	async fn can_build_big_pallet() {
		if std::option_env!("TEST_WS").is_none() {
			return
		}
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				transport: std::option_env!("TEST_WS").unwrap().to_owned().into(),
				pallets: vec!["Staking".to_owned()],
				child_trie: false,
				..Default::default()
			}))
			.build()
			.await
			.unwrap()
			.execute_with(|| {});
	}

	#[tokio::test(flavor = "multi_thread")]
	async fn can_fetch_all() {
		if std::option_env!("TEST_WS").is_none() {
			return
		}
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				transport: std::option_env!("TEST_WS").unwrap().to_owned().into(),
				..Default::default()
			}))
			.build()
			.await
			.unwrap()
			.execute_with(|| {});
	}
}
