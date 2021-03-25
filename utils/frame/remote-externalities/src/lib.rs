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
//!                 <frame_system::Pallet<Runtime>>::block_hash(3098545u32),
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
//! ```

use std::{
	fs,
	path::{Path, PathBuf},
};
use log::*;
use sp_core::hashing::twox_128;
pub use sp_io::TestExternalities;
use sp_core::{
	hexdisplay::HexDisplay,
	storage::{StorageKey, StorageData},
};
use codec::{Encode, Decode};
use jsonrpsee_http_client::{HttpClient, HttpConfig};

use sp_runtime::traits::Block as BlockT;

type KeyPair = (StorageKey, StorageData);

const LOG_TARGET: &str = "remote-ext";
const TARGET: &str = "http://localhost:9933";

jsonrpsee_proc_macros::rpc_client_api! {
	RpcApi<B: BlockT> {
		#[rpc(method = "state_getPairs", positional_params)]
		fn storage_pairs(prefix: StorageKey, hash: Option<B::Hash>) -> Vec<(StorageKey, StorageData)>;
		#[rpc(method = "chain_getFinalizedHead")]
		fn finalized_head() -> B::Hash;
	}
}

/// The execution mode.
#[derive(Clone)]
pub enum Mode<B: BlockT> {
	/// Online.
	Online(OnlineConfig<B>),
	/// Offline. Uses a state snapshot file and needs not any client config.
	Offline(OfflineConfig),
}

/// configuration of the online execution.
///
/// A state snapshot config must be present.
#[derive(Clone)]
pub struct OfflineConfig {
	/// The configuration of the state snapshot file to use. It must be present.
	pub state_snapshot: SnapshotConfig,
}

/// Configuration of the online execution.
///
/// A state snapshot config may be present and will be written to in that case.
#[derive(Clone)]
pub struct OnlineConfig<B: BlockT> {
	/// The HTTP uri to use.
	pub uri: String,
	/// The block number at which to connect. Will be latest finalized head if not provided.
	pub at: Option<B::Hash>,
	/// An optional state snapshot file to WRITE to, not for reading. Not written if set to `None`.
	pub state_snapshot: Option<SnapshotConfig>,
	/// The modules to scrape. If empty, entire chain state will be scraped.
	pub modules: Vec<String>,
}

impl<B: BlockT> Default for OnlineConfig<B> {
	fn default() -> Self {
		Self { uri: TARGET.to_owned(), at: None, state_snapshot: None, modules: Default::default() }
	}
}

impl<B: BlockT> OnlineConfig<B> {
	/// Return a new http rpc client.
	fn rpc(&self) -> HttpClient {
		HttpClient::new(&self.uri, HttpConfig { max_request_body_size: u32::MAX })
			.expect("valid HTTP url; qed")
	}
}

/// Configuration of the state snapshot.
#[derive(Clone)]
pub struct SnapshotConfig {
	// TODO: I could mix these two into one filed, but I think separate is better bc one can be
	// configurable while one not.
	/// File name.
	pub name: String,
	/// Base directory.
	pub directory: String,
}

impl Default for SnapshotConfig {
	fn default() -> Self {
		Self { name: "SNAPSHOT".into(), directory: ".".into() }
	}
}

impl SnapshotConfig {
	fn path(&self) -> PathBuf {
		Path::new(&self.directory).join(self.name.clone())
	}
}

/// Builder for remote-externalities.
pub struct Builder<B: BlockT> {
	inject: Vec<KeyPair>,
	mode: Mode<B>,
}

impl<B: BlockT> Default for Builder<B> {
	fn default() -> Self {
		Self {
			inject: Default::default(),
			mode: Mode::Online(OnlineConfig::default()),
		}
	}
}

// Mode methods
impl<B: BlockT> Builder<B> {
	fn as_online(&self) -> &OnlineConfig<B> {
		match &self.mode {
			Mode::Online(config) => &config,
			_ => panic!("Unexpected mode: Online"),
		}
	}

	fn as_online_mut(&mut self) -> &mut OnlineConfig<B> {
		match &mut self.mode {
			Mode::Online(config) => config,
			_ => panic!("Unexpected mode: Online"),
		}
	}
}

// RPC methods
impl<B: BlockT> Builder<B> {
	async fn rpc_get_head(&self) -> Result<B::Hash, &'static str> {
		trace!(target: LOG_TARGET, "rpc: finalized_head");
		RpcApi::<B>::finalized_head(&self.as_online().rpc()).await.map_err(|e| {
			error!("Error = {:?}", e);
			"rpc finalized_head failed."
		})
	}

	/// Relay the request to `state_getPairs` rpc endpoint.
	///
	/// Note that this is an unsafe RPC.
	async fn rpc_get_pairs(
		&self,
		prefix: StorageKey,
		at: B::Hash,
	) -> Result<Vec<KeyPair>, &'static str> {
		trace!(target: LOG_TARGET, "rpc: storage_pairs: {:?} / {:?}", prefix, at);
		RpcApi::<B>::storage_pairs(&self.as_online().rpc(), prefix, Some(at)).await.map_err(|e| {
			error!("Error = {:?}", e);
			"rpc storage_pairs failed"
		})
	}
}

// Internal methods
impl<B: BlockT> Builder<B> {
	/// Save the given data as state snapshot.
	fn save_state_snapshot(&self, data: &[KeyPair], path: &Path) -> Result<(), &'static str> {
		info!(target: LOG_TARGET, "writing to state snapshot file {:?}", path);
		fs::write(path, data.encode()).map_err(|_| "fs::write failed.")?;
		Ok(())
	}

	/// initialize `Self` from state snapshot. Panics if the file does not exist.
	fn load_state_snapshot(&self, path: &Path) -> Result<Vec<KeyPair>, &'static str> {
		info!(target: LOG_TARGET, "scraping keypairs from state snapshot {:?}", path,);
		let bytes = fs::read(path).map_err(|_| "fs::read failed.")?;
		Decode::decode(&mut &*bytes).map_err(|_| "decode failed")
	}

	/// Build `Self` from a network node denoted by `uri`.
	async fn load_remote(&self) -> Result<Vec<KeyPair>, &'static str> {
		let config = self.as_online();
		let at = self
			.as_online()
			.at
			.expect("online config must be initialized by this point; qed.")
			.clone();
		info!(target: LOG_TARGET, "scraping keypairs from remote node {} @ {:?}", config.uri, at);

		let keys_and_values = if config.modules.len() > 0 {
			let mut filtered_kv = vec![];
			for f in config.modules.iter() {
				let hashed_prefix = StorageKey(twox_128(f.as_bytes()).to_vec());
				let module_kv = self.rpc_get_pairs(hashed_prefix.clone(), at).await?;
				info!(
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
			info!(target: LOG_TARGET, "downloading data for all modules.");
			self.rpc_get_pairs(StorageKey(vec![]), at).await?.into_iter().collect::<Vec<_>>()
		};

		Ok(keys_and_values)
	}

	async fn init_remote_client(&mut self) -> Result<(), &'static str> {
		info!(target: LOG_TARGET, "initializing remote client to {:?}", self.as_online().uri);
		if self.as_online().at.is_none() {
			let at = self.rpc_get_head().await?;
			self.as_online_mut().at = Some(at);
		}
		Ok(())
	}

	async fn pre_build(mut self) -> Result<Vec<KeyPair>, &'static str> {
		let mut base_kv = match self.mode.clone() {
			Mode::Offline(config) => self.load_state_snapshot(&config.state_snapshot.path())?,
			Mode::Online(config) => {
				self.init_remote_client().await?;
				let kp = self.load_remote().await?;
				if let Some(c) = config.state_snapshot {
					self.save_state_snapshot(&kp, &c.path())?;
				}
				kp
			}
		};

		info!(
			target: LOG_TARGET,
			"extending externalities with {} manually injected keys",
			self.inject.len()
		);
		base_kv.extend(self.inject.clone());
		Ok(base_kv)
	}
}

// Public methods
impl<B: BlockT> Builder<B> {
	/// Create a new builder.
	pub fn new() -> Self {
		Default::default()
	}

	/// Inject a manual list of key and values to the storage.
	pub fn inject(mut self, injections: &[KeyPair]) -> Self {
		for i in injections {
			self.inject.push(i.clone());
		}
		self
	}

	/// Configure a state snapshot to be used.
	pub fn mode(mut self, mode: Mode<B>) -> Self {
		self.mode = mode;
		self
	}

	/// Build the test externalities.
	pub async fn build(self) -> Result<TestExternalities, &'static str> {
		let kv = self.pre_build().await?;
		let mut ext = TestExternalities::new_empty();

		info!(target: LOG_TARGET, "injecting a total of {} keys", kv.len());
		for (k, v) in kv {
			let (k, v) = (k.0, v.0);
			ext.insert(k, v);
		}
		Ok(ext)
	}
}

#[cfg(test)]
mod test_prelude {
	pub(crate) use super::*;
	pub(crate) use sp_runtime::testing::{H256 as Hash, Block as RawBlock, ExtrinsicWrapper};

	pub(crate) type Block = RawBlock<ExtrinsicWrapper<Hash>>;

	pub(crate) fn init_logger() {
		let _ = env_logger::Builder::from_default_env()
			.format_module_path(false)
			.format_level(true)
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
				state_snapshot: SnapshotConfig { name: "test_data/proxy_test".into(), ..Default::default() },
			}))
			.build()
			.await
			.expect("Can't read state snapshot file")
			.execute_with(|| {});
	}
}

#[cfg(all(test, feature = "remote-test"))]
mod remote_tests {
	use super::test_prelude::*;

	#[tokio::test]
	async fn can_build_one_pallet() {
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				modules: vec!["Proxy".into()],
				..Default::default()
			}))
			.build()
			.await
			.expect("Can't reach the remote node. Is it running?")
			.execute_with(|| {});
	}

	#[tokio::test]
	async fn can_create_state_snapshot() {
		init_logger();
		Builder::<Block>::new()
			.mode(Mode::Online(OnlineConfig {
				state_snapshot: Some(SnapshotConfig {
					name: "test_snapshot_to_remove.bin".into(),
					..Default::default()
				}),
				..Default::default()
			}))
			.build()
			.await
			.expect("Can't reach the remote node. Is it running?")
			.unwrap()
			.execute_with(|| {});

		let to_delete = std::fs::read_dir(SnapshotConfig::default().directory)
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
	async fn can_build_all() {
		init_logger();
		Builder::<Block>::new()
			.build()
			.await
			.expect("Can't reach the remote node. Is it running?")
			.execute_with(|| {});
	}
}
