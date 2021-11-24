// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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
use jsonrpsee_ws_client::{types::v2::params::JsonRpcParams, WsClient, WsClientBuilder};
use log::*;
use sp_core::{
	hashing::twox_128,
	hexdisplay::HexDisplay,
	storage::{
		well_known_keys::{is_default_child_storage_key, DEFAULT_CHILD_STORAGE_KEY_PREFIX},
		ChildInfo, PrefixedStorageKey, StorageData, StorageKey,
	},
};
pub use sp_io::TestExternalities;
use sp_runtime::{traits::Block as BlockT, StateVersion};
use std::{
	fs,
	path::{Path, PathBuf},
};

pub mod rpc_api;

type KeyPair = (StorageKey, StorageData);
type TopKeyPairs = Vec<KeyPair>;
type ChildKeyPairs = Vec<(ChildInfo, Vec<KeyPair>)>;

const LOG_TARGET: &str = "remote-ext";
const DEFAULT_TARGET: &str = "wss://rpc.polkadot.io";
const BATCH_SIZE: usize = 512;
const PAGE: u32 = BATCH_SIZE as u32;

jsonrpsee_proc_macros::rpc_client_api! {
	RpcApi<B: BlockT> {
		#[rpc(method = "childstate_getKeys", positional_params)]
		fn child_get_keys(
			child_key: PrefixedStorageKey,
			prefix: StorageKey,
			hash: Option<B::Hash>,
		) -> Vec<StorageKey>;
		#[rpc(method = "childstate_getStorage", positional_params)]
		fn child_get_storage(
			child_key: PrefixedStorageKey,
			prefix: StorageKey,
			hash: Option<B::Hash>,
		) -> StorageData;

		#[rpc(method = "state_getStorage", positional_params)]
		fn get_storage(prefix: StorageKey, hash: Option<B::Hash>) -> StorageData;
		#[rpc(method = "state_getKeysPaged", positional_params)]
		fn get_keys_paged(
			prefix: Option<StorageKey>,
			count: u32,
			start_key: Option<StorageKey>,
			hash: Option<B::Hash>,
		) -> Vec<StorageKey>;

		#[rpc(method = "chain_getFinalizedHead", positional_params)]
		fn finalized_head() -> B::Hash;
	}
}

/// The execution mode.
#[derive(Clone)]
pub enum Mode<B: BlockT> {
	/// Online. Potentially writes to a cache file.
	Online(OnlineConfig<B>),
	/// Offline. Uses a state snapshot file and needs not any client config.
	Offline(OfflineConfig),
	/// Prefer using a cache file if it exists, else use a remote server.
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
#[derive(Debug)]
pub struct Transport {
	uri: String,
	client: Option<WsClient>,
}

impl Clone for Transport {
	fn clone(&self) -> Self {
		Self { uri: self.uri.clone(), client: None }
	}
}

impl From<String> for Transport {
	fn from(t: String) -> Self {
		Self { uri: t, client: None }
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
	/// The pallets to scrape. If empty, entire chain state will be scraped.
	pub pallets: Vec<String>,
	/// Lookout for child-keys, and scrape them as well if set to true.
	pub scrape_children: bool,
	/// Transport config.
	pub transport: Transport,
}

impl<B: BlockT> OnlineConfig<B> {
	/// Return rpc (ws) client.
	fn rpc_client(&self) -> &WsClient {
		self.transport
			.client
			.as_ref()
			.expect("ws client must have been initialized by now; qed.")
	}
}

impl<B: BlockT> Default for OnlineConfig<B> {
	fn default() -> Self {
		Self {
			transport: Transport { uri: DEFAULT_TARGET.to_owned(), client: None },
			scrape_children: true,
			at: None,
			state_snapshot: None,
			pallets: vec![],
		}
	}
}

impl<B: BlockT> From<String> for OnlineConfig<B> {
	fn from(s: String) -> Self {
		Self { transport: s.into(), ..Default::default() }
	}
}

/// Configuration of the state snapshot.
#[derive(Clone)]
pub struct SnapshotConfig {
	/// The path to the snapshot file.
	pub path: PathBuf,
}

impl<P: Into<PathBuf>> From<P> for SnapshotConfig {
	fn from(p: P) -> Self {
		Self { path: p.into() }
	}
}

impl SnapshotConfig {
	pub fn new<P: Into<PathBuf>>(path: P) -> Self {
		Self { path: path.into() }
	}
}

impl Default for SnapshotConfig {
	fn default() -> Self {
		Self { path: Path::new("SNAPSHOT").into() }
	}
}

/// Builder for remote-externalities.
pub struct Builder<B: BlockT> {
	/// Custom key-pairs to be injected into the externalities. The *hashed* keys and values must
	/// be given.
	hashed_key_values: Vec<KeyPair>,
	/// Storage entry key prefixes to be injected into the externalities. The *hashed* prefix must
	/// be given.
	hashed_prefixes: Vec<Vec<u8>>,
	/// Storage entry keys to be injected into the externalities. The *hashed* key must be given.
	hashed_keys: Vec<Vec<u8>>,
	/// The keys that will be excluded from the final externality. The *hashed* key must be given.
	hashed_blacklist: Vec<Vec<u8>>,
	/// connectivity mode, online or offline.
	mode: Mode<B>,
	/// The state version being used.
	state_version: StateVersion,
}

// NOTE: ideally we would use `DefaultNoBound` here, but not worth bringing in frame-support for
// that.
impl<B: BlockT> Default for Builder<B> {
	fn default() -> Self {
		Self {
			mode: Default::default(),
			hashed_key_values: Default::default(),
			hashed_prefixes: Default::default(),
			hashed_keys: Default::default(),
			hashed_blacklist: Default::default(),
			state_version: StateVersion::V1,
		}
	}
}

// Mode methods
impl<B: BlockT> Builder<B> {
	fn as_online(&self) -> &OnlineConfig<B> {
		match &self.mode {
			Mode::Online(config) => &config,
			Mode::OfflineOrElseOnline(_, config) => &config,
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
impl<B: BlockT> Builder<B> {
	async fn rpc_get_storage(
		&self,
		key: StorageKey,
		maybe_at: Option<B::Hash>,
	) -> Result<StorageData, &'static str> {
		log::trace!(target: LOG_TARGET, "rpc: get_storage");
		RpcApi::<B>::get_storage(self.as_online().rpc_client(), key, maybe_at)
			.await
			.map_err(|e| {
				log::error!(target: LOG_TARGET, "Error = {:?}", e);
				"rpc get_storage failed."
			})
	}
	/// Get the latest finalized head.
	async fn rpc_get_head(&self) -> Result<B::Hash, &'static str> {
		log::trace!(target: LOG_TARGET, "rpc: finalized_head");
		RpcApi::<B>::finalized_head(self.as_online().rpc_client()).await.map_err(|e| {
			log::error!(target: LOG_TARGET, "Error = {:?}", e);
			"rpc finalized_head failed."
		})
	}

	/// Get all the keys at `prefix` at `hash` using the paged, safe RPC methods.
	async fn get_keys_paged(
		&self,
		prefix: StorageKey,
		at: B::Hash,
	) -> Result<Vec<StorageKey>, &'static str> {
		let mut last_key: Option<StorageKey> = None;
		let mut all_keys: Vec<StorageKey> = vec![];
		let keys = loop {
			let page = RpcApi::<B>::get_keys_paged(
				self.as_online().rpc_client(),
				Some(prefix.clone()),
				PAGE,
				last_key.clone(),
				Some(at),
			)
			.await
			.map_err(|e| {
				log::error!(target: LOG_TARGET, "Error = {:?}", e);
				"rpc get_keys failed"
			})?;
			let page_len = page.len();

			all_keys.extend(page);

			if page_len < PAGE as usize {
				log::debug!(target: LOG_TARGET, "last page received: {}", page_len);
				break all_keys
			} else {
				let new_last_key =
					all_keys.last().expect("all_keys is populated; has .last(); qed");
				log::debug!(
					target: LOG_TARGET,
					"new total = {}, full page received: {:?}",
					all_keys.len(),
					HexDisplay::from(new_last_key)
				);
				last_key = Some(new_last_key.clone());
			}
		};

		Ok(keys)
	}

	/// Synonym of `rpc_get_pairs_unsafe` that uses paged queries to first get the keys, and then
	/// map them to values one by one.
	///
	/// This can work with public nodes. But, expect it to be darn slow.
	pub(crate) async fn rpc_get_pairs_paged(
		&self,
		prefix: StorageKey,
		at: B::Hash,
	) -> Result<Vec<KeyPair>, &'static str> {
		use jsonrpsee_ws_client::types::traits::Client;
		use serde_json::to_value;
		let keys = self.get_keys_paged(prefix, at).await?;
		let keys_count = keys.len();
		log::debug!(target: LOG_TARGET, "Querying a total of {} keys", keys.len());

		let mut key_values: Vec<KeyPair> = vec![];
		let client = self.as_online().rpc_client();
		for chunk_keys in keys.chunks(BATCH_SIZE) {
			let batch = chunk_keys
				.iter()
				.cloned()
				.map(|key| {
					(
						"state_getStorage",
						JsonRpcParams::Array(vec![
							to_value(key).expect("json serialization will work; qed."),
							to_value(at).expect("json serialization will work; qed."),
						]),
					)
				})
				.collect::<Vec<_>>();

			let values = client.batch_request::<Option<StorageData>>(batch).await.map_err(|e| {
				log::error!(
					target: LOG_TARGET,
					"failed to execute batch: {:?}. Error: {:?}",
					chunk_keys.iter().map(|k| HexDisplay::from(k)).collect::<Vec<_>>(),
					e
				);
				"batch failed."
			})?;

			assert_eq!(chunk_keys.len(), values.len());

			for (idx, key) in chunk_keys.into_iter().enumerate() {
				let maybe_value = values[idx].clone();
				let value = maybe_value.unwrap_or_else(|| {
					log::warn!(target: LOG_TARGET, "key {:?} had none corresponding value.", &key);
					StorageData(vec![])
				});
				key_values.push((key.clone(), value));
				if key_values.len() % (10 * BATCH_SIZE) == 0 {
					let ratio: f64 = key_values.len() as f64 / keys_count as f64;
					log::debug!(
						target: LOG_TARGET,
						"progress = {:.2} [{} / {}]",
						ratio,
						key_values.len(),
						keys_count,
					);
				}
			}
		}

		Ok(key_values)
	}
}

// Internal methods
impl<B: BlockT> Builder<B> {
	/// Save the given data to the top keys snapshot.
	fn save_top_snapshot(&self, data: &[KeyPair], path: &PathBuf) -> Result<(), &'static str> {
		let mut path = path.clone();
		path.set_extension("top");
		debug!(target: LOG_TARGET, "writing to state snapshot file {:?}", path);
		fs::write(path, data.encode()).map_err(|_| "fs::write failed.")?;
		Ok(())
	}

	/// Save the given data to the child keys snapshot.
	fn save_child_snapshot(
		&self,
		data: &ChildKeyPairs,
		path: &PathBuf,
	) -> Result<(), &'static str> {
		let mut path = path.clone();
		path.set_extension("child");
		debug!(target: LOG_TARGET, "writing to state snapshot file {:?}", path);
		fs::write(path, data.encode()).map_err(|_| "fs::write failed.")?;
		Ok(())
	}

	fn load_top_snapshot(&self, path: &PathBuf) -> Result<TopKeyPairs, &'static str> {
		let mut path = path.clone();
		path.set_extension("top");
		info!(target: LOG_TARGET, "loading top key-pairs from snapshot {:?}", path);
		let bytes = fs::read(path).map_err(|_| "fs::read failed.")?;
		Decode::decode(&mut &*bytes).map_err(|_| "decode failed")
	}

	fn load_child_snapshot(&self, path: &PathBuf) -> Result<ChildKeyPairs, &'static str> {
		let mut path = path.clone();
		path.set_extension("child");
		info!(target: LOG_TARGET, "loading child key-pairs from snapshot {:?}", path);
		let bytes = fs::read(path).map_err(|_| "fs::read failed.")?;
		Decode::decode(&mut &*bytes).map_err(|_| "decode failed")
	}

	/// Load all of the child keys from the remote config, given the already scraped list of top key
	/// pairs.
	///
	/// Stores all values to cache as well, if provided.
	async fn load_child_keys_remote_and_maybe_save(
		&self,
		top_kv: &[KeyPair],
	) -> Result<Vec<(ChildInfo, Vec<KeyPair>)>, &'static str> {
		let child_kv = self.load_child_keys_remote(&top_kv).await?;
		if let Some(c) = &self.as_online().state_snapshot {
			self.save_child_snapshot(&child_kv, &c.path)?;
		}
		Ok(child_kv)
	}

	/// Load all of the child keys from the remote config, given the already scraped list of top key
	/// pairs.
	async fn load_child_keys_remote(
		&self,
		top_kv: &[KeyPair],
	) -> Result<Vec<(ChildInfo, Vec<KeyPair>)>, &'static str> {
		let child_bearing_top_keys = top_kv
			.iter()
			.filter_map(
				|(k, _)| {
					if is_default_child_storage_key(k.as_ref()) {
						Some(k)
					} else {
						None
					}
				},
			)
			.collect::<Vec<_>>();

		info!(
			target: LOG_TARGET,
			"👩‍👦 scraping child-tree data from {} top keys",
			child_bearing_top_keys.len()
		);

		let mut child_kvs = vec![];
		for prefixed_top_key in child_bearing_top_keys {
			let child_keys = RpcApi::<B>::child_get_keys(
				self.as_online().rpc_client(),
				PrefixedStorageKey::new(prefixed_top_key.as_ref().to_vec()),
				StorageKey(vec![]),
				self.as_online().at,
			)
			.await
			.map_err(|e| {
				error!(target: LOG_TARGET, "Error = {:?}", e);
				"rpc child_get_keys failed."
			})?;

			debug!(
				target: LOG_TARGET,
				"scraped {} child-keys of the child-bearing top key: {:?}",
				child_keys.len(),
				HexDisplay::from(prefixed_top_key)
			);

			let mut child_kv = vec![];
			for child_key in child_keys {
				let child_value = RpcApi::<B>::child_get_storage(
					self.as_online().rpc_client(),
					PrefixedStorageKey::new(prefixed_top_key.as_ref().to_vec()),
					child_key.clone(),
					self.as_online().at,
				)
				.await
				.map_err(|e| {
					error!(target: LOG_TARGET, "Error = {:?}", e);
					"rpc child_get_storage failed."
				})?;
				child_kv.push((child_key, child_value));
			}

			// super tricky.
			let un_prefixed = &prefixed_top_key.0[DEFAULT_CHILD_STORAGE_KEY_PREFIX.len()..];
			child_kvs.push((ChildInfo::new_default(&un_prefixed), child_kv));
		}

		Ok(child_kvs)
	}

	/// Load all the `top` keys from the remote config, and maybe write then to cache.
	async fn load_top_keys_remote_and_maybe_save(&self) -> Result<Vec<KeyPair>, &'static str> {
		let top_kv = self.load_top_keys_remote().await?;
		if let Some(c) = &self.as_online().state_snapshot {
			self.save_top_snapshot(&top_kv, &c.path)?;
		}
		Ok(top_kv)
	}

	/// Load all the `top` keys from the remote config.
	async fn load_top_keys_remote(&self) -> Result<Vec<KeyPair>, &'static str> {
		let config = self.as_online();
		let at = self
			.as_online()
			.at
			.expect("online config must be initialized by this point; qed.")
			.clone();
		log::info!(target: LOG_TARGET, "scraping key-pairs from remote @ {:?}", at);

		let mut keys_and_values = if config.pallets.len() > 0 {
			let mut filtered_kv = vec![];
			for f in config.pallets.iter() {
				let hashed_prefix = StorageKey(twox_128(f.as_bytes()).to_vec());
				let module_kv = self.rpc_get_pairs_paged(hashed_prefix.clone(), at).await?;
				log::info!(
					target: LOG_TARGET,
					"downloaded data for module {} (count: {} / prefix: {:?}).",
					f,
					module_kv.len(),
					HexDisplay::from(&hashed_prefix),
				);
				filtered_kv.extend(module_kv);
			}
			filtered_kv
		} else {
			log::info!(target: LOG_TARGET, "downloading data for all pallets.");
			self.rpc_get_pairs_paged(StorageKey(vec![]), at).await?
		};

		for prefix in &self.hashed_prefixes {
			log::info!(
				target: LOG_TARGET,
				"adding data for hashed prefix: {:?}",
				HexDisplay::from(prefix)
			);
			let additional_key_values =
				self.rpc_get_pairs_paged(StorageKey(prefix.to_vec()), at).await?;
			keys_and_values.extend(additional_key_values);
		}

		for key in &self.hashed_keys {
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
		let mut online = self.as_online_mut();
		log::debug!(target: LOG_TARGET, "initializing remote client to {:?}", online.transport.uri);

		// First, initialize the ws client.
		let ws_client = WsClientBuilder::default()
			.max_request_body_size(u32::MAX)
			.build(&online.transport.uri)
			.await
			.map_err(|e| {
				log::error!(target: LOG_TARGET, "{:?}", e);
				"failed to build ws client"
			})?;
		online.transport.client = Some(ws_client);

		// Then, if `at` is not set, set it.
		if self.as_online().at.is_none() {
			let at = self.rpc_get_head().await?;
			self.as_online_mut().at = Some(at);
		}

		Ok(())
	}

	pub(crate) async fn pre_build(
		mut self,
	) -> Result<(Vec<KeyPair>, Vec<(ChildInfo, Vec<KeyPair>)>), &'static str> {
		let mode = self.mode.clone();
		let mut top_kv = match mode {
			Mode::Offline(config) => self.load_top_snapshot(&config.state_snapshot.path)?,
			Mode::Online(_) => {
				self.init_remote_client().await?;
				self.load_top_keys_remote_and_maybe_save().await?
			},
			Mode::OfflineOrElseOnline(offline_config, _) => {
				if let Ok(top_kv) = self.load_top_snapshot(&offline_config.state_snapshot.path) {
					top_kv
				} else {
					self.init_remote_client().await?;
					self.load_top_keys_remote_and_maybe_save().await?
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

		let child_kv = match self.mode.clone() {
			Mode::Online(ref config) if config.scrape_children =>
				self.load_child_keys_remote_and_maybe_save(&top_kv).await?,
			Mode::Offline(ref config) => self
				.load_child_snapshot(&config.state_snapshot.path)
				.map_err(|why| {
					log::warn!(target: LOG_TARGET, "failed to load child-key file due to {:?}", why)
				})
				.unwrap_or_default(),
			Mode::OfflineOrElseOnline(ref offline_config, ref online_config)
				if online_config.scrape_children =>
			{
				if let Ok(child_kv) = self.load_child_snapshot(&offline_config.state_snapshot.path)
				{
					child_kv
				} else {
					self.load_child_keys_remote_and_maybe_save(&top_kv).await?
				}
			},
			_ => Default::default(),
		};

		Ok((top_kv, child_kv))
	}
}

// Public methods
impl<B: BlockT> Builder<B> {
	/// Create a new builder.
	pub fn new() -> Self {
		Default::default()
	}

	/// Inject a manual list of key and values to the storage.
	pub fn inject_hashed_key_value(mut self, injections: &[KeyPair]) -> Self {
		for i in injections {
			self.hashed_key_values.push(i.clone());
		}
		self
	}
	/// Inject a hashed prefix. This is treated as-is, and should be pre-hashed.
	///
	/// This should be used to inject a "PREFIX", like a storage (double) map.
	pub fn inject_hashed_prefix(mut self, hashed: &[u8]) -> Self {
		self.hashed_prefixes.push(hashed.to_vec());
		self
	}

	/// Inject a hashed key to scrape. This is treated as-is, and should be pre-hashed.
	///
	/// This should be used to inject a "KEY", like a storage value.
	pub fn inject_hashed_key(mut self, hashed: &[u8]) -> Self {
		self.hashed_keys.push(hashed.to_vec());
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

	/// overwrite the `at` value, if `mode` is set to [`Mode::Online`].
	///
	/// noop if `mode` is [`Mode::Offline`]
	pub fn overwrite_online_at(mut self, at: B::Hash) -> Self {
		if let Mode::Online(mut online) = self.mode.clone() {
			online.at = Some(at);
			self.mode = Mode::Online(online);
		}
		self
	}

	/// Build the test externalities.
	pub async fn build(self) -> Result<TestExternalities, &'static str> {
		let state_version = self.state_version.clone();
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
			child_kv.iter().map(|(_, kv)| kv).flatten().count()
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

		Ok(ext)
	}
}

#[cfg(test)]
mod test_prelude {
	pub(crate) use super::*;
	pub(crate) use sp_runtime::testing::{Block as RawBlock, ExtrinsicWrapper, H256 as Hash};

	pub(crate) type Block = RawBlock<ExtrinsicWrapper<Hash>>;

	pub(crate) fn init_logger() {
		let _ = env_logger::Builder::from_default_env()
			.format_module_path(true)
			.format_level(true)
			.filter_module(LOG_TARGET, log::LevelFilter::Debug)
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
			.mode(Mode::Offline(OfflineConfig {
				state_snapshot: SnapshotConfig::new("test_data/proxy_test"),
			}))
			.build()
			.await
			.expect("Can't read state snapshot file")
			.execute_with(|| {});
	}

	#[tokio::test]
	async fn can_exclude_from_cache() {
		init_logger();

		// get the first key from the cache file.
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

	const REMOTE_INACCESSIBLE: &'static str = "Can't reach the remote node. Is it running?";

	#[tokio::test]
	async fn offline_else_online_works() {
		init_logger();
		// this shows that in the second run, we use the remote and create a cache.
		Builder::<Block>::new()
			.mode(Mode::OfflineOrElseOnline(
				OfflineConfig {
					state_snapshot: SnapshotConfig::new("test_snapshot_to_remove.bin"),
				},
				OnlineConfig {
					pallets: vec!["Proxy".to_owned()],
					state_snapshot: Some(SnapshotConfig::new("test_snapshot_to_remove.bin")),
					..Default::default()
				},
			))
			.build()
			.await
			.expect(REMOTE_INACCESSIBLE)
			.execute_with(|| {});

		// this shows that in the second run, we are not using the remote
		Builder::<Block>::new()
			.mode(Mode::OfflineOrElseOnline(
				OfflineConfig {
					state_snapshot: SnapshotConfig::new("test_snapshot_to_remove.bin"),
				},
				OnlineConfig {
					pallets: vec!["Proxy".to_owned()],
					state_snapshot: Some(SnapshotConfig::new("test_snapshot_to_remove.bin")),
					transport: "ws://non-existent:666".to_owned().into(),
					..Default::default()
				},
			))
			.build()
			.await
			.expect(REMOTE_INACCESSIBLE)
			.execute_with(|| {});
	}

	#[tokio::test]
	async fn can_build_one_pallet() {
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				pallets: vec!["Proxy".to_owned()],
				..Default::default()
			}))
			.build()
			.await
			.expect(REMOTE_INACCESSIBLE)
			.execute_with(|| {});
	}

	#[tokio::test]
	async fn can_build_few_pallet() {
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				transport: "wss://kusama-rpc.polkadot.io".to_owned().into(),
				pallets: vec!["Proxy".to_owned(), "Multisig".to_owned()],
				..Default::default()
			}))
			.build()
			.await
			.expect(REMOTE_INACCESSIBLE)
			.execute_with(|| {});

		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				transport: "wss://rpc.polkadot.io".to_owned().into(),
				pallets: vec!["Proxy".to_owned(), "Multisig".to_owned()],
				..Default::default()
			}))
			.build()
			.await
			.expect(REMOTE_INACCESSIBLE)
			.execute_with(|| {});
	}

	#[tokio::test]
	async fn can_create_state_snapshot() {
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				state_snapshot: Some(SnapshotConfig::new("test_snapshot_to_remove.bin")),
				pallets: vec!["Proxy".to_owned()],
				..Default::default()
			}))
			.build()
			.await
			.expect(REMOTE_INACCESSIBLE)
			.execute_with(|| {});

		let to_delete = std::fs::read_dir(Path::new("."))
			.unwrap()
			.into_iter()
			.map(|d| d.unwrap())
			.filter(|p| p.path().extension().unwrap_or_default() == "bin")
			.collect::<Vec<_>>();

		assert!(to_delete.len() > 0);

		for d in to_delete {
			std::fs::remove_file(d.path()).unwrap();
		}
	}

	#[tokio::test]
	#[ignore = "takes too much time on average."]
	async fn can_fetch_all() {
		init_logger();
		Builder::<Block>::new()
			.build()
			.await
			.expect(REMOTE_INACCESSIBLE)
			.execute_with(|| {});
	}

	#[tokio::test]
	async fn can_build_child_tree() {
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				// transport: "wss://kusama-rpc.polkadot.io".to_owned().into(),
				transport: "ws://kianenigma-archive:9924".to_owned().into(),
				// transport: "ws://localhost:9999".to_owned().into(),
				pallets: vec!["Crowdloan".to_owned()],
				..Default::default()
			}))
			.build()
			.await
			.expect(REMOTE_INACCESSIBLE)
			.execute_with(|| {});
	}
}
