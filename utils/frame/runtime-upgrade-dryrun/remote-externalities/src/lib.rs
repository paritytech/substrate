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
//! based chain, or a local cache file.
//!
//! #### Runtime to Test Against
//!
//! While not absolutely necessary, you most likely need a `Runtime` equivalent in your test setup
//! through which you can infer storage types. There are two options here:
//!
//! 1. Build a mock runtime, similar how to you would build one in a pallet test (see example
//!    below). The very important point here is that this mock needs to hold real values for types
//!    that matter for you, based on the chain of interest. Some typical ones are:
//!
//! - `sp_runtime::AccountId32` as `AccountId`.
//! - `u32` as `BlockNumber`.
//! - `u128` as Balance.
//!
//! Once you have your `Runtime`, you can use it for storage type resolution and do things like
//! `<my_pallet::Pallet<Runtime>>::storage_getter()` or `<my_pallet::StorageItem<Runtime>>::get()`.
//!
//! 2. Or, you can use a real runtime.
//!
//! ### Example
//!
//! With a test runtime
//!
//! ```ignore
//! use remote_externalities::Builder;
//!
//! #[derive(Clone, Eq, PartialEq, Debug, Default)]
//! pub struct TestRuntime;
//!
//! use frame_system as system;
//! impl_outer_origin! {
//!     pub enum Origin for TestRuntime {}
//! }
//!
//! impl frame_system::Config for TestRuntime {
//!     ..
//!     // we only care about these two for now. The rest can be mock. The block number type of
//!     // kusama is u32.
//!     type BlockNumber = u32;
//!     type Header = Header;
//!     ..
//! }
//!
//! #[test]
//! fn test_runtime_works() {
//!     let hash: Hash =
//!         hex!["f9a4ce984129569f63edc01b1c13374779f9384f1befd39931ffdcc83acf63a7"].into();
//!     let parent: Hash =
//!         hex!["540922e96a8fcaf945ed23c6f09c3e189bd88504ec945cc2171deaebeaf2f37e"].into();
//!     Builder::new()
//!         .at(hash)
//!         .module("System")
//!         .build()
//!         .execute_with(|| {
//!             assert_eq!(
//!                 // note: the hash corresponds to 3098546. We can check only the parent.
//!                 // https://polkascan.io/kusama/block/3098546
//!                 <frame_system::Module<Runtime>>::block_hash(3098545u32),
//!                 parent,
//!             )
//!         });
//! }
//! ```
//!
//! Or with the real kusama runtime.
//!
//! ```ignore
//! use remote_externalities::Builder;
//! use kusama_runtime::Runtime;
//!
//! #[test]
//! fn test_runtime_works() {
//!     let hash: Hash =
//!         hex!["f9a4ce984129569f63edc01b1c13374779f9384f1befd39931ffdcc83acf63a7"].into();
//!     Builder::new()
//!         .at(hash)
//!         .module("Staking")
//!         .build()
//!         .execute_with(|| assert_eq!(<pallet_staking::Module<Runtime>>::validator_count(), 400));
//! }
//!```

use std::{
	fs,
	path::{Path, PathBuf},
};
use std::fmt::{Debug, Formatter, Result as FmtResult};
use log::*;
use sp_core::{hashing::twox_128};
pub use sp_io::TestExternalities;
use sp_core::storage::{StorageKey, StorageData};
use jsonrpsee_http_client::{HttpClient, HttpConfig};
use jsonrpsee_types::jsonrpc::{Params, to_value as to_json_value};

// TODO: this should ideally not be hardcoded.
type Hash = sp_core::H256;
type KeyPair = (StorageKey, StorageData);

const LOG_TARGET: &'static str = "remote-ext";

/// Struct for better hex printing of slice types.
pub struct HexSlice<'a>(&'a [u8]);

impl<'a> HexSlice<'a> {
	pub fn new<T>(data: &'a T) -> HexSlice<'a>
	where
		T: ?Sized + AsRef<[u8]> + 'a,
	{
		HexSlice(data.as_ref())
	}
}

// You can choose to implement multiple traits, like Lower and UpperHex
impl Debug for HexSlice<'_> {
	fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
		write!(f, "0x")?;
		for byte in self.0 {
			write!(f, "{:x}", byte)?;
		}
		Ok(())
	}
}

/// Extension trait for hex display.
pub trait HexDisplayExt {
	fn hex_display(&self) -> HexSlice<'_>;
}

impl<T: ?Sized + AsRef<[u8]>> HexDisplayExt for T {
	fn hex_display(&self) -> HexSlice<'_> {
		HexSlice::new(self)
	}
}

#[derive(Copy, Clone, Debug)]
/// Basic configuration for the cache behavior.
pub enum CacheMode {
	/// Use the cache if it is there, else create it.
	UseElseCreate,
	/// Force a new cache to be created from remote, then use it.
	ForceUpdate,
	/// None. Use remote and don't create anything.
	None,
}

/// The name of the cache file configuration.
pub enum CacheName {
	/// It will be {chain_name},{hash},{modules?}.bin
	Auto,
	/// Forced to the given file name.
	Forced(String),
}

/// Builder for remote-externalities.
pub struct Builder {
	at: Option<Hash>,
	uri: String,
	inject: Vec<KeyPair>,
	module_filter: Vec<String>,
	cache_config: CacheMode,
	cache_name_config: CacheName,
	client: Option<HttpClient>,
	chain: String,
}

impl Default for Builder {
	fn default() -> Self {
		Self {
			uri: "http://localhost:9933".into(),
			at: Default::default(),
			inject: Default::default(),
			module_filter: Default::default(),
			cache_config: CacheMode::None,
			cache_name_config: CacheName::Auto,
			client: None,
			chain: "UNSET".into(),
		}
	}
}

// RPC methods
impl Builder {
	async fn rpc_get_head(&self) -> Hash {
		let json_value = self
			.rpc_client()
			.request("chain_getFinalizedHead", Params::None)
			.await
			.expect("get chain finalized head request failed");
		jsonrpsee_types::jsonrpc::from_value(json_value).unwrap()
	}

	/// Relay the request to `state_getPairs` rpc endpoint.
	///
	/// Note that this is an unsafe RPC.
	async fn rpc_get_pairs(&self, prefix: StorageKey, at: Hash) -> Vec<KeyPair> {
		let serialized_prefix = to_json_value(prefix).expect("StorageKey serialization infallible");
		let at = to_json_value(at).expect("Block hash serialization infallible");
		let json_value = self
			.rpc_client()
			.request("state_getPairs", Params::Array(vec![serialized_prefix, at]))
			.await
			.expect("Storage state_getPairs failed");
		jsonrpsee_types::jsonrpc::from_value(json_value).unwrap()
	}

	/// Get the chain name.
	async fn chain_name(&self) -> String {
		let json_value = self
			.rpc_client()
			.request("system_chain", Params::None)
			.await
			.expect("system_chain failed");
		jsonrpsee_types::jsonrpc::from_value(json_value).unwrap()
	}

	fn rpc_client(&self) -> &HttpClient {
		self.client.as_ref().expect("Client initialized after `build`; qed")
	}
}

// Internal methods
impl Builder {
	/// The file name associated with this scrape.
	fn final_cache_name(&self) -> String {
		match &self.cache_name_config {
			CacheName::Auto => {
				format!("{},{:?},{}.bin", self.chain, self.final_at(), self.module_filter.join(","))
			}
			CacheName::Forced(name) => name.clone(),
		}
	}

	/// Directory at which to create the cache. Not configurable for now.
	// TODO
	fn cache_dir() -> &'static str {
		"."
	}

	/// The final path of the cache.
	fn cache_path(&self) -> PathBuf {
		Path::new(Self::cache_dir()).join(self.final_cache_name())
	}

	/// Save the given data as cache.
	fn save_cache(&self, data: &[KeyPair]) {
		let bdata = bincode::serialize(data).unwrap();
		let path = self.cache_path();
		info!(target: LOG_TARGET, "writing to cache file {:?}", path);
		fs::write(path, bdata).unwrap();
	}

	/// Try and initialize `Self` from cache
	fn try_scrape_cached(&self) -> Result<Vec<KeyPair>, &'static str> {
		info!(
			target: LOG_TARGET,
			"scraping keypairs from cache {:?} @ {:?}",
			self.cache_path(),
			self.final_at()
		);
		let path = self.cache_path();
		fs::read(path)
			.map_err(|_| "failed to read cache")
			.and_then(|b| bincode::deserialize(&b[..]).map_err(|_| "failed to decode cache"))
	}

	/// Get the final `at` that shall be used.
	///
	/// This should be only called after a call to [`build`].
	fn final_at(&self) -> Hash {
		self.at.expect("At intialized after `built`; qed")
	}

	/// Build `Self` from a network node denoted by `uri`.
	async fn scrape_remote(&self) -> Vec<KeyPair> {
		let at = self.final_at();
		info!(target: LOG_TARGET, "scraping keypairs from remote node {} @ {:?}", self.uri, at);

		let mut keys_and_values = if self.module_filter.len() > 0 {
			let mut filtered_kv = vec![];
			for f in self.module_filter.iter() {
				let hashed_prefix = StorageKey(twox_128(f.as_bytes()).to_vec());
				let module_kv = self.rpc_get_pairs(hashed_prefix.clone(), at).await;
				info!(
					target: LOG_TARGET,
					"downloaded data for module {} (count: {} / prefix: {:?}).",
					f,
					module_kv.len(),
					hashed_prefix.hex_display(),
				);
				filtered_kv.extend(module_kv);
			}
			filtered_kv
		} else {
			info!(target: LOG_TARGET, "downloading data for all modules.");
			self.rpc_get_pairs(StorageKey(vec![]), at).await.into_iter().collect::<Vec<_>>()
		};

		// concat any custom key values.
		keys_and_values.extend(self.inject.clone());
		keys_and_values
	}

	async fn force_update(&self) -> Vec<KeyPair> {
		let kp = self.scrape_remote().await;
		self.save_cache(&kp);
		kp
	}

	async fn init_remote_client(&mut self) {
		self.client = Some(
			HttpClient::new(
				self.uri.clone(),
				HttpConfig { max_request_body_size: u32::max_value() },
			)
			.unwrap(),
		);
		self.at = match self.at {
			Some(at) => Some(at),
			None => Some(self.rpc_get_head().await),
		};
		self.chain = self.chain_name().await;
	}

	async fn pre_build(mut self) -> Vec<KeyPair> {
		match self.cache_config {
			CacheMode::None => {
				self.init_remote_client().await;
				self.scrape_remote().await
			},
			CacheMode::ForceUpdate => {
				self.init_remote_client().await;
				self.force_update().await
			},
			CacheMode::UseElseCreate => match self.try_scrape_cached() {
				Ok(kp) => kp,
				Err(why) => {
					self.init_remote_client().await;
					warn!(target: LOG_TARGET, "failed to load cache due to {:?}", why);
					self.force_update().await
				}
			},
		}
	}
}

// Public methods
impl Builder {
	/// Create a new builder.
	pub fn new() -> Self {
		Default::default()
	}

	/// Scrape the chain at the given block hash.
	///
	/// If not set, latest finalized will be used.
	pub fn at(mut self, at: Hash) -> Self {
		self.at = Some(at);
		self
	}

	/// Look for a chain at the given URI.
	///
	/// If not set, `ws://localhost:9944` will be used.
	pub fn uri(mut self, uri: String) -> Self {
		self.uri = uri;
		self
	}

	/// Inject a manual list of key and values to the storage.
	pub fn inject(mut self, injections: &[KeyPair]) -> Self {
		for i in injections {
			self.inject.push(i.clone());
		}
		self
	}

	/// Scrape only this module.
	///
	/// If used multiple times, all of the given modules will be used, else the entire chain.
	pub fn module(mut self, module: &str) -> Self {
		self.module_filter.push(module.to_string());
		self
	}

	/// Configure a cache to be used.
	pub fn cache_mode(mut self, mode: CacheMode) -> Self {
		self.cache_config = mode;
		self
	}

	/// Configure the name of the cache file.
	pub fn cache_name(mut self, name: CacheName) -> Self {
		self.cache_name_config = name;
		self
	}

	/// Build the test externalities.
	pub async fn build(self) -> TestExternalities {
		let kv = self.pre_build().await;
		let mut ext = TestExternalities::new_empty();

		info!(target: LOG_TARGET, "injecting a total of {} keys", kv.len());
		for (k, v) in kv {
			let (k, v) = (k.0, v.0);
			trace!(target: LOG_TARGET, "injecting {:?} -> {:?}", k.hex_display(), v.hex_display());
			ext.insert(k, v);
		}
		ext
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	const TEST_URI: &'static str = "http://localhost:9933";

	#[derive(Clone, Eq, PartialEq, Debug, Default)]
	pub struct TestRuntime;

	#[tokio::test]
	#[cfg(feature = "remote-test")]
	async fn can_build_system() {
		let _ = env_logger::Builder::from_default_env()
			.format_module_path(false)
			.format_level(true)
			.try_init();

		Builder::new().uri(TEST_URI.into()).module("System").build().await.execute_with(|| {});
	}

	#[tokio::test]
	async fn can_load_cache() {
		let _ = env_logger::Builder::from_default_env()
			.format_module_path(false)
			.format_level(true)
			.try_init();

		Builder::new()
			.uri(TEST_URI.into())
			.cache_mode(CacheMode::UseElseCreate)
			.cache_name(CacheName::Forced("test_cache".into()))
			.build()
			.await
			.execute_with(|| {});
	}

	#[tokio::test]
	#[cfg(feature = "remote-test")]
	async fn can_create_cache() {
		let _ = env_logger::Builder::from_default_env()
			.format_module_path(false)
			.format_level(true)
			.try_init();

		Builder::new()
			.uri(TEST_URI.into())
			.cache_mode(CacheMode::UseElseCreate)
			.module("System")
			.build()
			.await
			.execute_with(|| {});

		let to_delete = std::fs::read_dir(Builder::cache_dir())
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
	#[cfg(feature = "remote-test")]
	async fn can_build_all() {
		let _ = env_logger::Builder::from_default_env()
			.format_module_path(true)
			.format_level(true)
			.try_init();

		Builder::new().uri(TEST_URI.into()).build().await.execute_with(|| {});
	}
}
